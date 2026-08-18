import ErdosProblems.Erdos140.Quantitative
import ErdosProblems.Erdos140.ReachableIteration
import ErdosProblems.Erdos140.GroupCount
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The finite-cyclic Kelley--Meka counting interface

The analytic part of the Kelley--Meka/Bloom--Sisask proof is most naturally
carried out in the odd cyclic group `ZMod (2 * N + 1)`.  This file isolates
the exact quantitative statement required from that argument and proves the
normalization-sensitive passage back to the interval `[1,N]`.

The density parameter is required to be positive.  This is essential: at
parameter zero the putative lower bound would be `N^2`, which already fails
for the full interval when `N >= 2`.
-/

open Finset
open scoped NNReal

namespace Erdos140

/-- The group-level output to be supplied by the Bohr-set density iteration.

The ambient group is exactly the no-wrap group `ZMod (2*N+1)`.  Its density
scale uses the group cardinality, not the interval length. -/
def KelleyMekaCyclicCountHypothesis (K : ℝ) : Prop :=
  0 < K ∧
    ∀ (N : ℕ), 1 ≤ N →
      ∀ (A : Finset (ZMod (intervalModulus N))), A.Nonempty →
        ∀ d : ℕ, 1 ≤ d →
          Real.log (((intervalModulus N : ℕ) : ℝ) / (#A : ℝ)) ≤
              (d : ℝ) * Real.log 2 →
            Real.exp (-K * (d : ℝ) ^ 12) *
                ((intervalModulus N : ℕ) : ℝ) ^ 2 ≤
              (threeAPCount A : ℝ)

/-! ## The actual initial regular-Bohr restriction -/

/-- Empty frequency data presents the whole finite group as a rank-zero Bohr
carrier at every scale.  This is the honest starting datum for the located
restriction iteration. -/
noncomputable def universalBohrData (G : Type*) [AddCommGroup G] : BohrData G where
  freq := ∅
  width := fun _ ↦ 0

@[simp] theorem universalBohrData_rank (G : Type*) [AddCommGroup G] :
    BohrData.rank (universalBohrData G) = 0 := by
  change (∅ : Finset (AddCharacter G)).card = 0
  simp

@[simp] theorem universalBohrData_carrier (G : Type*) [AddCommGroup G] [Fintype G]
    (rho : ℝ≥0) :
    ((universalBohrData G).dilate rho).carrier = (Finset.univ : Finset G) := by
  classical
  ext x
  simp [BohrData.mem_carrier, universalBohrData]

@[simp] theorem universalBohrData_carrier_self
    (G : Type*) [AddCommGroup G] [Fintype G] :
    (universalBohrData G).carrier = (Finset.univ : Finset G) := by
  simpa using universalBohrData_carrier G 1

/-- The initial regular restriction has ambient carrier the whole odd cyclic
group and restricted set exactly `A`. -/
noncomputable def cyclicInitialRestriction (N : ℕ)
    (A : Finset (ZMod (intervalModulus N))) (hA : A.Nonempty) :
    BohrStopping.RegularRestriction (ZMod (intervalModulus N)) where
  bohr := universalBohrData (ZMod (intervalModulus N))
  outer := 1
  inner := 1
  regular := by
    refine ⟨by norm_num, by norm_num, ?_⟩
    simp only [universalBohrData_carrier]
    omega
  set := A
  nonempty := hA
  subset_carrier := by
    intro x hx
    rw [universalBohrData_carrier]
    simp

@[simp] theorem cyclicInitialRestriction_density (N : ℕ)
    (A : Finset (ZMod (intervalModulus N))) (hA : A.Nonempty) :
    (cyclicInitialRestriction N A hA).density =
      (#A : ℝ) / (intervalModulus N : ℕ) := by
  simp [BohrStopping.RegularRestriction.density,
    BohrStopping.RegularRestriction.ambient, cyclicInitialRestriction]

@[simp] theorem cyclicInitialRestriction_rank (N : ℕ)
    (A : Finset (ZMod (intervalModulus N))) (hA : A.Nonempty) :
    (cyclicInitialRestriction N A hA).rank = 0 := by
  simp [BohrStopping.RegularRestriction.rank, cyclicInitialRestriction]

@[simp] theorem cyclicInitialRestriction_card (N : ℕ)
    (A : Finset (ZMod (intervalModulus N))) (hA : A.Nonempty) :
    (cyclicInitialRestriction N A hA).card = intervalModulus N := by
  simp [BohrStopping.RegularRestriction.card,
    BohrStopping.RegularRestriction.ambient, cyclicInitialRestriction]

/-- The located version of the initial restriction records the identity
translation into the original cyclic set. -/
noncomputable def cyclicInitialLocated (N : ℕ)
    (A : Finset (ZMod (intervalModulus N))) (hA : A.Nonempty) :
    DensityStep.LocatedRestriction A where
  restriction := cyclicInitialRestriction N A hA
  shift := 0
  subset_original := by
    intro x hx
    simpa [cyclicInitialRestriction] using hx

@[simp] theorem cyclicInitialLocated_density (N : ℕ)
    (A : Finset (ZMod (intervalModulus N))) (hA : A.Nonempty) :
    (cyclicInitialLocated N A hA).density =
      (#A : ℝ) / (intervalModulus N : ℕ) := by
  exact cyclicInitialRestriction_density N A hA

@[simp] theorem cyclicInitialLocated_rank (N : ℕ)
    (A : Finset (ZMod (intervalModulus N))) (hA : A.Nonempty) :
    (cyclicInitialLocated N A hA).rank = 0 := by
  exact cyclicInitialRestriction_rank N A hA

@[simp] theorem cyclicInitialLocated_card (N : ℕ)
    (A : Finset (ZMod (intervalModulus N))) (hA : A.Nonempty) :
    (cyclicInitialLocated N A hA).card = intervalModulus N := by
  exact cyclicInitialRestriction_card N A hA

/-- An unconditional maximal chain of provenance-preserving restrictions.
The terminal state has no further controlled located restriction, which is
the form of maximality consumed by the analytic balanced-restriction theorem. -/
theorem exists_maximalLocatedChain
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {original : Finset G} {q sizeCost : ℝ} {rankCost fuel : ℕ}
    (hq : 0 ≤ q) (s : DensityStep.LocatedRestriction original)
    (hgrowth : 1 < q ^ fuel * s.density) :
    ∃ n ≤ fuel, ∃ t : DensityStep.LocatedRestriction original,
      DensityStep.LocatedControlledChain q rankCost sizeCost n s t ∧
      (¬ ∃ u : DensityStep.LocatedRestriction original,
        BohrStopping.IsControlledIncrement q rankCost sizeCost
          t.restriction u.restriction) ∧
      q ^ n * s.density ≤ t.density ∧
      t.rank ≤ s.rank + n * rankCost ∧
      Real.exp (-(n : ℝ) * sizeCost) * (s.card : ℝ) ≤ (t.card : ℝ) := by
  let Bad : DensityStep.LocatedRestriction original → Prop := fun t ↦
    ∃ u : DensityStep.LocatedRestriction original,
      BohrStopping.IsControlledIncrement q rankCost sizeCost
        t.restriction u.restriction
  have hbad : DensityStep.ProducesLocatedIncrement Bad q rankCost sizeCost := by
    intro t ht
    exact ht
  simpa [Bad] using
    DensityStep.exists_stopping_located_chain hq hbad fuel s hgrowth

/-- One thousand twenty-four increments by the fixed factor `1025/1024` pay for
one dyadic density unit.  This is the explicit growth estimate used by the
located maximal chain, with no asymptotic constants hidden. -/
lemma fixedIncrement_growth_of_dyadicScale
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {original : Finset G} {d : ℕ}
    (s : DensityStep.LocatedRestriction original)
    (hscale : BohrStopping.OnDyadicScale d s.density) :
    1 < (1025 / 1024 : ℝ) ^ (1024 * (d + 1)) * s.density := by
  have hbase : (2 : ℝ) ≤ (1025 / 1024 : ℝ) ^ 1024 := by
    have h := one_add_mul_le_pow (a := (1 / 1024 : ℝ)) (by norm_num) 1024
    norm_num at h
    exact h
  have hpow : (2 : ℝ) ^ (d + 1) ≤
      (1025 / 1024 : ℝ) ^ (1024 * (d + 1)) := by
    calc
      (2 : ℝ) ^ (d + 1) ≤ ((1025 / 1024 : ℝ) ^ 1024) ^ (d + 1) :=
        pow_le_pow_left₀ (by positivity) hbase (d + 1)
      _ = (1025 / 1024 : ℝ) ^ (1024 * (d + 1)) := by rw [← pow_mul]
  change 1 / (2 : ℝ) ^ d ≤ s.density at hscale
  have hmul := mul_le_mul hpow hscale (by positivity) (by positivity)
  have hleft : (2 : ℝ) ^ (d + 1) * (1 / (2 : ℝ) ^ d) = 2 := by
    rw [pow_succ]
    field_simp
  rw [hleft] at hmul
  linarith

/-- The fixed-factor maximal located chain specialized to the `1025/1024`
increment used by the concrete narrowing step. -/
theorem exists_fixedIncrement_maximalLocatedChain
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {original : Finset G} {d rankCost : ℕ} {sizeCost : ℝ}
    (s : DensityStep.LocatedRestriction original)
    (hscale : BohrStopping.OnDyadicScale d s.density) :
    ∃ n ≤ 1024 * (d + 1), ∃ t : DensityStep.LocatedRestriction original,
      DensityStep.LocatedControlledChain (1025 / 1024 : ℝ) rankCost sizeCost n s t ∧
      (¬ ∃ u : DensityStep.LocatedRestriction original,
        BohrStopping.IsControlledIncrement (1025 / 1024 : ℝ) rankCost sizeCost
          t.restriction u.restriction) ∧
      (1025 / 1024 : ℝ) ^ n * s.density ≤ t.density ∧
      t.rank ≤ s.rank + n * rankCost ∧
      Real.exp (-(n : ℝ) * sizeCost) * (s.card : ℝ) ≤ (t.card : ℝ) := by
  exact exists_maximalLocatedChain (by norm_num) s
    (fixedIncrement_growth_of_dyadicScale s hscale)

/-- The concrete terminal certificate produced by balanced restriction and
Hölder lifting.  Every field is an actual finite-set fact; in particular the
two support fields retain the translation back into the original set. -/
structure CyclicHolderCertificate (N : ℕ)
    (A : Finset (ZMod (intervalModulus N))) (K : ℝ) (d : ℕ) where
  A' : Finset (ZMod (intervalModulus N))
  A'' : Finset (ZMod (intervalModulus N))
  B : Finset (ZMod (intervalModulus N))
  B' : Finset (ZMod (intervalModulus N))
  translate : ZMod (intervalModulus N)
  alpha : ℝ
  p : ℕ
  f : ZMod (intervalModulus N) → ℝ
  A'_nonempty : A'.Nonempty
  A''_nonempty : A''.Nonempty
  B_nonempty : B.Nonempty
  A''_subset_B' : A'' ⊆ B'
  A'_sub_translate : ∀ x ∈ A', x - translate ∈ A
  A''_sub_translate : ∀ x ∈ A'', x - translate ∈ A
  alpha_nonneg : 0 ≤ alpha
  A'_density : alpha * (#B : ℝ) ≤ (#A' : ℝ)
  A''_density : alpha * (#B' : ℝ) ≤ (#A'' : ℝ)
  p_pos : 0 < p
  doubled_density :
    (2 / 3 : ℝ) ^ p ≤ HolderLifting.relativeDensity A'' B'
  approximation :
    |(GroupCount.normalizedMixedProgression A' A'' -
        (Fintype.card (ZMod (intervalModulus N)) : ℝ) / (#B : ℝ)) -
        HolderLifting.pairing f (GroupCount.doubledFinset A'')| ≤
      ((Fintype.card (ZMod (intervalModulus N)) : ℝ) / (#B : ℝ)) / 8
  balanced_moment :
    HolderLifting.localMoment (GroupCount.doubledFinset B') p f ≤
      (((Fintype.card (ZMod (intervalModulus N)) : ℝ) / (#B : ℝ)) / 8) ^ p
  quantitative_size :
    Real.exp (-K * (d : ℝ) ^ 12) *
        (Fintype.card (ZMod (intervalModulus N)) : ℝ) ^ 2 ≤
      alpha ^ 3 * (#B : ℝ) * (#B' : ℝ) / 2

/-- Raw terminal output expected from the fixed-state analytic argument at a
maximal located restriction.  It records exactly the fibre-density and two
child-cardinality bounds; the global twelfth-power bookkeeping is proved in
this file. -/
structure LocatedHolderTerminalData
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {original : Finset G} (t : DensityStep.LocatedRestriction original)
    (K : ℝ) (d : ℕ) where
  certificate : GroupCount.HolderCountCertificate original
  alpha_lower : (3 / 4 : ℝ) * t.density ≤ certificate.alpha
  B_card : Real.exp (-(K * ((d + 1 : ℕ) : ℝ) ^ 11)) *
      (t.card : ℝ) ≤ (#certificate.B : ℝ)
  B'_card : Real.exp (-(K * ((d + 1 : ℕ) : ℝ) ^ 11)) *
      (t.card : ℝ) ≤ (#certificate.B' : ℝ)

namespace LocatedHolderTerminalData

/-- Package the exact terminal output of the dense-pair/Holder argument.
The fixed narrowing loss `epsilon = 1/8` leaves density `7/8`, which is
uniformly at least the `3/4` retained by the global bookkeeping.  The two
one-step cardinality bounds are copied from the concrete narrowing package. -/
noncomputable def ofDensePair
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {original : Finset G} (t : DensityStep.LocatedRestriction original)
    {K : ℝ} {d rankCost p : ℕ}
    (P : DensityStep.NarrowingPackage t (1 / 8 : ℝ)
      (K * ((d + 1 : ℕ) : ℝ) ^ 11) rankCost)
    (hdense : DensityStep.HasDensePair t P.childOne P.childTwo (1 / 8 : ℝ))
    (hp : 0 < p) (f : G → ℝ)
    (hpDensity : (2 / 3 : ℝ) ^ p ≤
      GroupCount.densePairDensity t (1 / 8 : ℝ))
    (happrox :
      |(GroupCount.normalizedMixedProgression
            (GroupCount.densePairEndpointSet P hdense)
            (GroupCount.densePairMiddleSet P hdense) -
          (Fintype.card G : ℝ) / (#P.childOne.carrier : ℝ)) -
          HolderLifting.pairing f
            (GroupCount.doubledFinset
              (GroupCount.densePairMiddleSet P hdense))| ≤
        ((Fintype.card G : ℝ) / (#P.childOne.carrier : ℝ)) / 8)
    (hbalanced :
      BalancedRestriction.weightedLpNorm
          (normalizedIndicator
            (GroupCount.doubledFinset P.childTwo.carrier)) f p ≤
        ((Fintype.card G : ℝ) / (#P.childOne.carrier : ℝ)) / 8) :
    LocatedHolderTerminalData t K d := by
  let c := GroupCount.holderCountCertificateOfDensePair t P hdense
    (by norm_num) (by norm_num) hp f hpDensity happrox hbalanced
  refine
    { certificate := c
      alpha_lower := ?_
      B_card := ?_
      B'_card := ?_ }
  · change (3 / 4 : ℝ) * t.density ≤
      GroupCount.densePairDensity t (1 / 8 : ℝ)
    simp only [GroupCount.densePairDensity]
    nlinarith [t.density_pos.le]
  · change Real.exp (-(K * ((d + 1 : ℕ) : ℝ) ^ 11)) *
        (t.card : ℝ) ≤ (#P.childOne.carrier : ℝ)
    exact P.cardOne
  · change Real.exp (-(K * ((d + 1 : ℕ) : ℝ) ^ 11)) *
        (t.card : ℝ) ≤ (#P.childTwo.carrier : ℝ)
    exact P.cardTwo

end LocatedHolderTerminalData

namespace CyclicHolderCertificate

private lemma exp_neg_one_le_half : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
  have he : (2 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_two.le
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-1)).le
  have hprod : Real.exp 1 * Real.exp (-1) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [hprod] at hm
  exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    (by simpa [mul_comm] using hm)

/-- A dyadic density lower bound, after the harmless `3/4` fibre loss,
dominates a uniform twelfth-power exponential. -/
theorem density_cube_bound_of_dyadic
    {d : ℕ} (hd : 1 ≤ d) {alpha : ℝ}
    (halpha : (3 / 4 : ℝ) * (1 / (2 : ℝ) ^ d) ≤ alpha) :
    Real.exp (-(8 : ℝ) * (d : ℝ) ^ 12) ≤ alpha ^ 3 / 2 := by
  let m : ℕ := 8 * d ^ 12
  have hexp : Real.exp (-(8 : ℝ) * (d : ℝ) ^ 12) =
      Real.exp (-1) ^ m := by
    rw [show -(8 : ℝ) * (d : ℝ) ^ 12 = (m : ℝ) * (-1) by
      simp [m], Real.exp_nat_mul]
  have hhalf : Real.exp (-1) ^ m ≤ (1 / 2 : ℝ) ^ m :=
    pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_one_le_half m
  have hdPow : d ≤ d ^ 12 := Nat.le_pow (by norm_num)
  have hm : 3 * d + 3 ≤ m := by
    dsimp [m]
    omega
  have hdecay : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ (3 * d + 3) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
  have hcoeff : (1 / 2 : ℝ) ^ (3 * d + 3) ≤
      ((3 / 4 : ℝ) * (1 / (2 : ℝ) ^ d)) ^ 3 / 2 := by
    rw [pow_add, pow_mul]
    ring_nf
    rw [show (1 / 8 : ℝ) = (1 / 2 : ℝ) ^ 3 by norm_num, ← pow_mul]
    gcongr
    all_goals norm_num [Nat.mul_comm]
  calc
    Real.exp (-(8 : ℝ) * (d : ℝ) ^ 12) = Real.exp (-1) ^ m := hexp
    _ ≤ (1 / 2 : ℝ) ^ m := hhalf
    _ ≤ (1 / 2 : ℝ) ^ (3 * d + 3) := hdecay
    _ ≤ ((3 / 4 : ℝ) * (1 / (2 : ℝ) ^ d)) ^ 3 / 2 := hcoeff
    _ ≤ alpha ^ 3 / 2 := by gcongr

/-- Add the single global quantitative-size inequality to the generic
located Holder certificate produced by `GroupCount`.  All translation and
normalization-sensitive fields are copied without reinterpretation. -/
def ofHolderCountCertificate {N : ℕ}
    {A : Finset (ZMod (intervalModulus N))} {K : ℝ} {d : ℕ}
    (c : GroupCount.HolderCountCertificate A)
    (hsize : Real.exp (-K * (d : ℝ) ^ 12) *
        (Fintype.card (ZMod (intervalModulus N)) : ℝ) ^ 2 ≤
      c.alpha ^ 3 * (#c.B : ℝ) * (#c.B' : ℝ) / 2) :
    CyclicHolderCertificate N A K d where
  A' := c.A'
  A'' := c.A''
  B := c.B
  B' := c.B'
  translate := c.translate
  alpha := c.alpha
  p := c.p
  f := c.f
  A'_nonempty := c.A'_nonempty
  A''_nonempty := c.A''_nonempty
  B_nonempty := c.B_nonempty
  A''_subset_B' := c.A''_subset_B'
  A'_sub_translate := c.A'_sub_translate
  A''_sub_translate := c.A''_sub_translate
  alpha_nonneg := c.alpha_nonneg
  A'_density := c.A'_density
  A''_density := c.A''_density
  p_pos := c.p_pos
  doubled_density := c.doubled_density
  approximation := c.approximation
  balanced_moment := c.balanced_moment
  quantitative_size := hsize

/-- Two separate Bohr-cardinality losses combine additively in the
exponential constant. -/
theorem bohr_product_of_individual_bounds
    {G : Type*} [Fintype G] {K₁ K₂ : ℝ} {d : ℕ} {B B' : Finset G}
    (hB : Real.exp (-K₁ * (d : ℝ) ^ 12) * (Fintype.card G : ℝ) ≤
      (#B : ℝ))
    (hB' : Real.exp (-K₂ * (d : ℝ) ^ 12) * (Fintype.card G : ℝ) ≤
      (#B' : ℝ)) :
    Real.exp (-(K₁ + K₂) * (d : ℝ) ^ 12) *
        (Fintype.card G : ℝ) ^ 2 ≤ (#B : ℝ) * (#B' : ℝ) := by
  calc
    Real.exp (-(K₁ + K₂) * (d : ℝ) ^ 12) *
          (Fintype.card G : ℝ) ^ 2 =
        (Real.exp (-K₁ * (d : ℝ) ^ 12) * (Fintype.card G : ℝ)) *
          (Real.exp (-K₂ * (d : ℝ) ^ 12) * (Fintype.card G : ℝ)) := by
      rw [show -(K₁ + K₂) * (d : ℝ) ^ 12 =
          -K₁ * (d : ℝ) ^ 12 + -K₂ * (d : ℝ) ^ 12 by ring,
        Real.exp_add]
      ring
    _ ≤ (#B : ℝ) * (#B' : ℝ) := by
      exact mul_le_mul hB hB' (by positivity) (by positivity)

/-- Multiplication of the density loss and the Bohr-cardinality loss.  This
small lemma keeps the final twelfth-power accounting independent of the
particular constants chosen by the structural theorem. -/
theorem quantitative_size_of_density_and_bohr
    {G : Type*} [Fintype G] {alpha Kdensity Kbohr : ℝ} {d : ℕ}
    {B B' : Finset G}
    (hdensity : Real.exp (-Kdensity * (d : ℝ) ^ 12) ≤ alpha ^ 3 / 2)
    (hbohr : Real.exp (-Kbohr * (d : ℝ) ^ 12) *
        (Fintype.card G : ℝ) ^ 2 ≤ (#B : ℝ) * (#B' : ℝ)) :
    Real.exp (-(Kdensity + Kbohr) * (d : ℝ) ^ 12) *
        (Fintype.card G : ℝ) ^ 2 ≤
      alpha ^ 3 * (#B : ℝ) * (#B' : ℝ) / 2 := by
  have hBnonneg : 0 ≤ (#B : ℝ) * (#B' : ℝ) := by positivity
  calc
    Real.exp (-(Kdensity + Kbohr) * (d : ℝ) ^ 12) *
          (Fintype.card G : ℝ) ^ 2 =
        Real.exp (-Kdensity * (d : ℝ) ^ 12) *
          (Real.exp (-Kbohr * (d : ℝ) ^ 12) *
            (Fintype.card G : ℝ) ^ 2) := by
      rw [show -(Kdensity + Kbohr) * (d : ℝ) ^ 12 =
          -Kdensity * (d : ℝ) ^ 12 + -Kbohr * (d : ℝ) ^ 12 by ring,
        Real.exp_add]
      ring
    _ ≤ Real.exp (-Kdensity * (d : ℝ) ^ 12) *
          ((#B : ℝ) * (#B' : ℝ)) :=
      mul_le_mul_of_nonneg_left hbohr (Real.exp_pos _).le
    _ ≤ (alpha ^ 3 / 2) * ((#B : ℝ) * (#B' : ℝ)) :=
      mul_le_mul_of_nonneg_right hdensity hBnonneg
    _ = alpha ^ 3 * (#B : ℝ) * (#B' : ℝ) / 2 := by ring

/-- A terminal certificate gives the desired cyclic progression count. -/
theorem count_bound {N : ℕ} {A : Finset (ZMod (intervalModulus N))}
    {K : ℝ} {d : ℕ} (c : CyclicHolderCertificate N A K d) :
    Real.exp (-K * (d : ℝ) ^ 12) *
        ((intervalModulus N : ℕ) : ℝ) ^ 2 ≤ (threeAPCount A : ℝ) := by
  letI : NeZero (intervalModulus N) := ⟨by simp [intervalModulus]⟩
  have hodd : Odd (intervalModulus N) := by
    exact ⟨N, by simp [intervalModulus, two_mul]⟩
  simpa using GroupCount.zmod_cyclic_count_bound_of_holder_density hodd
    c.A'_nonempty c.A''_nonempty c.B_nonempty c.A''_subset_B' c.translate
    c.A'_sub_translate c.A''_sub_translate c.alpha_nonneg c.A'_density
    c.A''_density c.p_pos c.f c.doubled_density c.approximation
    c.balanced_moment c.quantitative_size

end CyclicHolderCertificate

/-- Exact structural obligation left to the balanced-restriction layer. -/
def KelleyMekaHolderCertificateHypothesis (K : ℝ) : Prop :=
  0 < K ∧
    ∀ (N : ℕ), 1 ≤ N →
      ∀ (A : Finset (ZMod (intervalModulus N))), A.Nonempty →
        ∀ d : ℕ, 1 ≤ d →
          Real.log (((intervalModulus N : ℕ) : ℝ) / (#A : ℝ)) ≤
              (d : ℝ) * Real.log 2 →
            Nonempty (CyclicHolderCertificate N A K d)

/-- Exact fixed-state analytic obligation at the end of the actual located
maximal chain.  The theorem demanded here is local: once no further
`1025/1024`-increment of the advertised rank and size cost exists, it produces the
generic Holder fibre data and the two one-step child-cardinality bounds.
The dyadic-density and accumulated-rank premises are invariants proved by the
actual chain, so this interface does not quantify over unrelated restrictions.
All iteration and twelfth-power accounting remain proved in this file. -/
def KelleyMekaMaximalTerminalHypothesis (K : ℝ) : Prop :=
  0 < K ∧
    ∀ (N : ℕ), 1 ≤ N →
      ∀ (A : Finset (ZMod (intervalModulus N))), A.Nonempty →
        ∀ d : ℕ, 1 ≤ d →
          Real.log (((intervalModulus N : ℕ) : ℝ) / (#A : ℝ)) ≤
              (d : ℝ) * Real.log 2 →
            ∃ rankCost : ℕ,
              ∀ t : DensityStep.LocatedRestriction A,
                (1 / (2 : ℝ) ^ d) ≤ t.density →
                t.rank ≤ 1024 * (d + 1) * rankCost →
                (¬ ∃ u : DensityStep.LocatedRestriction A,
                  BohrStopping.IsControlledIncrement (1025 / 1024 : ℝ) rankCost
                    (K * ((d + 1 : ℕ) : ℝ) ^ 11)
                    t.restriction u.restriction) →
                Nonempty (LocatedHolderTerminalData t K d)

/-- Concrete output interface for the analytic density step.  This is kept
independent of `LocatedHolderTerminalData`: a downstream module can prove the
displayed existential directly without importing this file, and the central
assembly merely bundles its four fields.  Neither the interval size nor the
initial set otherwise enters the conclusion because the analytic statement is
local to a restriction satisfying the explicit density and rank invariants. -/
def KelleyMekaTerminalProducerHypothesis (K : ℝ) : Prop :=
  0 < K ∧
    ∀ (N : ℕ),
      ∀ (A : Finset (ZMod (intervalModulus N))), A.Nonempty →
        ∀ d : ℕ, 1 ≤ d →
          ∃ rankCost : ℕ,
            ∀ t : DensityStep.LocatedRestriction A,
              (1 / (2 : ℝ) ^ d) ≤ t.density →
              t.rank ≤ 1024 * (d + 1) * rankCost →
              (¬ ∃ u : DensityStep.LocatedRestriction A,
                BohrStopping.IsControlledIncrement (1025 / 1024 : ℝ) rankCost
                  (K * ((d + 1 : ℕ) : ℝ) ^ 11)
                  t.restriction u.restriction) →
              ∃ c : GroupCount.HolderCountCertificate A,
                (3 / 4 : ℝ) * t.density ≤ c.alpha ∧
                Real.exp (-(K * ((d + 1 : ℕ) : ℝ) ^ 11)) *
                    (t.card : ℝ) ≤ (#c.B : ℝ) ∧
                Real.exp (-(K * ((d + 1 : ℕ) : ℝ) ^ 11)) *
                    (t.card : ℝ) ≤ (#c.B' : ℝ)

/-- The raw analytic producer is exactly the local maximal-state theorem
needed by the finite stopping argument. -/
theorem maximalTerminal_of_terminalProducer
    {K : ℝ} (h : KelleyMekaTerminalProducerHypothesis K) :
    KelleyMekaMaximalTerminalHypothesis K := by
  refine ⟨h.1, ?_⟩
  intro N _hN A hA d hd _hlog
  obtain ⟨rankCost, hproduce⟩ := h.2 N A hA d hd
  refine ⟨rankCost, ?_⟩
  intro t hscale hrank hno
  obtain ⟨c, halpha, hB, hB'⟩ := hproduce t hscale hrank hno
  exact ⟨
    { certificate := c
      alpha_lower := halpha
      B_card := hB
      B'_card := hB' }⟩

/-- Balanced terminal certificates imply the exact cyclic counting theorem. -/
theorem cyclicCount_of_holderCertificates
    {K : ℝ} (h : KelleyMekaHolderCertificateHypothesis K) :
    KelleyMekaCyclicCountHypothesis K := by
  refine ⟨h.1, ?_⟩
  intro N hN A hA d hd hlog
  exact (Classical.choice (h.2 N hN A hA d hd hlog)).count_bound

/-- The numerical initial state associated to a subset of the odd cyclic
group.  Rank one is the trivial-character presentation of the whole group. -/
noncomputable def cyclicInitialState (N : ℕ)
    (A : Finset (ZMod (intervalModulus N))) : DensityIteration.State where
  density := (#A : ℝ) / (intervalModulus N : ℕ)
  rank := 1
  card := intervalModulus N

/-- Exact analytic input expected from the count-or-density-increment
proposition.  Unlike `DensityIteration.OneStepHypothesis`, this uses the
reachability-restricted interface, so it never asks about ambient cardinalities
larger than the starting cyclic group. -/
def KelleyMekaReachableOneStepHypothesis (K : ℝ) : Prop :=
  0 < K ∧
    ∀ (N : ℕ), 1 ≤ N →
      ∀ (A : Finset (ZMod (intervalModulus N))), A.Nonempty →
        ∀ d : ℕ, 1 ≤ d →
          Real.log (((intervalModulus N : ℕ) : ℝ) / (#A : ℝ)) ≤
              (d : ℝ) * Real.log 2 →
            ∃ rankCost : ℕ,
              ReachableIteration.OneStepHypothesis 2 rankCost
                (K * ((d + 1 : ℕ) : ℝ) ^ 11)
                (K * ((d + 1 : ℕ) : ℝ) ^ 11)
                (threeAPCount A : ℝ) (cyclicInitialState N A)

private lemma cyclicInitial_density_nonneg {N : ℕ}
    (A : Finset (ZMod (intervalModulus N))) :
    0 ≤ (cyclicInitialState N A).density := by
  change 0 ≤ (#A : ℝ) / (intervalModulus N : ℕ)
  positivity

private lemma cyclicInitial_density_le_one {N : ℕ} (_hN : 1 ≤ N)
    (A : Finset (ZMod (intervalModulus N))) :
    (cyclicInitialState N A).density ≤ 1 := by
  have hmod : 0 < intervalModulus N := by simp [intervalModulus]
  have hcard : #A ≤ intervalModulus N := by
    simpa using Finset.card_le_univ A
  simp only [cyclicInitialState]
  rw [div_le_one (by exact_mod_cast hmod)]
  exact_mod_cast hcard

private lemma cyclicInitial_onDyadicScale {N d : ℕ}
    (_hN : 1 ≤ N) {A : Finset (ZMod (intervalModulus N))} (hA : A.Nonempty)
    (hlog : Real.log (((intervalModulus N : ℕ) : ℝ) / (#A : ℝ)) ≤
      (d : ℝ) * Real.log 2) :
    DensityIteration.OnDyadicScale d (cyclicInitialState N A).density := by
  have hmodNat : 0 < intervalModulus N := by simp [intervalModulus]
  have hmod : (0 : ℝ) < intervalModulus N := by exact_mod_cast hmodNat
  have hcard : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
  have hratio : (0 : ℝ) <
      ((intervalModulus N : ℕ) : ℝ) / (#A : ℝ) := div_pos hmod hcard
  have hpow : (0 : ℝ) < (2 : ℝ) ^ d := pow_pos (by norm_num) _
  have hlog' :
      Real.log (((intervalModulus N : ℕ) : ℝ) / (#A : ℝ)) ≤
        Real.log ((2 : ℝ) ^ d) := by
    simpa [Real.log_pow] using hlog
  have hratio_le :
      (((intervalModulus N : ℕ) : ℝ) / (#A : ℝ)) ≤ (2 : ℝ) ^ d :=
    (Real.log_le_log_iff hratio hpow).mp hlog'
  have hmul : (((intervalModulus N : ℕ) : ℝ)) ≤
      (2 : ℝ) ^ d * (#A : ℝ) := (div_le_iff₀ hcard).mp hratio_le
  rw [DensityIteration.OnDyadicScale]
  simp only [cyclicInitialState]
  apply (div_le_div_iff₀ hpow hmod).2
  simpa [mul_comm] using hmul

private lemma cyclicInitialLocated_onDyadicScale {N d : ℕ}
    (hN : 1 ≤ N) {A : Finset (ZMod (intervalModulus N))} (hA : A.Nonempty)
    (hlog : Real.log (((intervalModulus N : ℕ) : ℝ) / (#A : ℝ)) ≤
      (d : ℝ) * Real.log 2) :
    BohrStopping.OnDyadicScale d (cyclicInitialLocated N A hA).density := by
  have h := cyclicInitial_onDyadicScale hN hA hlog
  simpa [DensityIteration.OnDyadicScale, BohrStopping.OnDyadicScale,
    cyclicInitialState] using h

/-- The exact provenance-preserving maximal chain available for every cyclic
input on dyadic scale `d`.  The analytic terminal theorem only needs to act
on the returned state with its explicit no-further-increment certificate. -/
theorem exists_cyclic_fixedIncrement_maximalLocatedChain
    {N d rankCost : ℕ} (hN : 1 ≤ N)
    {A : Finset (ZMod (intervalModulus N))} (hA : A.Nonempty)
    (hlog : Real.log (((intervalModulus N : ℕ) : ℝ) / (#A : ℝ)) ≤
      (d : ℝ) * Real.log 2)
    (sizeCost : ℝ) :
    ∃ n ≤ 1024 * (d + 1),
      ∃ t : DensityStep.LocatedRestriction A,
        DensityStep.LocatedControlledChain (1025 / 1024 : ℝ) rankCost sizeCost n
            (cyclicInitialLocated N A hA) t ∧
        (¬ ∃ u : DensityStep.LocatedRestriction A,
          BohrStopping.IsControlledIncrement (1025 / 1024 : ℝ) rankCost sizeCost
            t.restriction u.restriction) ∧
        (1025 / 1024 : ℝ) ^ n *
            (cyclicInitialLocated N A hA).density ≤ t.density ∧
        t.rank ≤ (cyclicInitialLocated N A hA).rank + n * rankCost ∧
        Real.exp (-(n : ℝ) * sizeCost) *
            ((cyclicInitialLocated N A hA).card : ℝ) ≤ (t.card : ℝ) := by
  exact exists_fixedIncrement_maximalLocatedChain (cyclicInitialLocated N A hA)
    (cyclicInitialLocated_onDyadicScale hN hA hlog)

private lemma add_one_pow_twelve_le {d : ℕ} (hd : 1 ≤ d) :
    ((d + 1 : ℕ) : ℝ) ^ 12 ≤ (2 : ℝ) ^ 12 * (d : ℝ) ^ 12 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hbase : ((d + 1 : ℕ) : ℝ) ≤ 2 * (d : ℝ) := by
    push_cast
    linarith
  calc
    ((d + 1 : ℕ) : ℝ) ^ 12 ≤ (2 * (d : ℝ)) ^ 12 :=
      pow_le_pow_left₀ (by positivity) hbase 12
    _ = (2 : ℝ) ^ 12 * (d : ℝ) ^ 12 := by rw [mul_pow]

namespace CyclicHolderCertificate

/-- One final child-cardinality loss, following at most `1024(d+1)` located
increments with the same eleventh-power step cost, is absorbed by the
twelfth-power constant `1025 * 2^12 * K`. -/
theorem child_card_bound_of_located_chain
    {G : Type*} [Fintype G] {K : ℝ} (hK : 0 ≤ K)
    {d n terminalCard : ℕ} (hd : 1 ≤ d) (hn : n ≤ 1024 * (d + 1))
    {B : Finset G}
    (hchain : Real.exp (-(n : ℝ) *
          (K * ((d + 1 : ℕ) : ℝ) ^ 11)) * (Fintype.card G : ℝ) ≤
        (terminalCard : ℝ))
    (hchild : Real.exp (-(K * ((d + 1 : ℕ) : ℝ) ^ 11)) *
        (terminalCard : ℝ) ≤ (#B : ℝ)) :
    Real.exp (-(1025 * (2 : ℝ) ^ 12 * K) * (d : ℝ) ^ 12) *
        (Fintype.card G : ℝ) ≤ (#B : ℝ) := by
  let step : ℝ := K * ((d + 1 : ℕ) : ℝ) ^ 11
  have hn' : n + 1 ≤ 1025 * (d + 1) := by omega
  have hnR : (n : ℝ) + 1 ≤ 1025 * ((d + 1 : ℕ) : ℝ) := by
    exact_mod_cast hn'
  have hstep : 0 ≤ step := by
    dsimp [step]
    positivity
  have hcostOne : ((n : ℝ) + 1) * step ≤
      1025 * K * ((d + 1 : ℕ) : ℝ) ^ 12 := by
    calc
      ((n : ℝ) + 1) * step ≤
          (1025 * ((d + 1 : ℕ) : ℝ)) * step :=
        mul_le_mul_of_nonneg_right hnR hstep
      _ = 1025 * K * ((d + 1 : ℕ) : ℝ) ^ 12 := by
        simp only [step]
        ring
  have hpow := add_one_pow_twelve_le hd
  have hcost : ((n : ℝ) + 1) * step ≤
      (1025 * (2 : ℝ) ^ 12 * K) * (d : ℝ) ^ 12 := by
    calc
      ((n : ℝ) + 1) * step ≤
          1025 * K * ((d + 1 : ℕ) : ℝ) ^ 12 := hcostOne
      _ ≤ 1025 * K * ((2 : ℝ) ^ 12 * (d : ℝ) ^ 12) :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg (by norm_num) hK)
      _ = (1025 * (2 : ℝ) ^ 12 * K) * (d : ℝ) ^ 12 := by ring
  have hcombined : Real.exp (-((n : ℝ) + 1) * step) *
      (Fintype.card G : ℝ) ≤ (#B : ℝ) := by
    calc
      Real.exp (-((n : ℝ) + 1) * step) * (Fintype.card G : ℝ) =
          Real.exp (-step) *
            (Real.exp (-(n : ℝ) * step) * (Fintype.card G : ℝ)) := by
        rw [show -((n : ℝ) + 1) * step =
            -step + (-(n : ℝ) * step) by ring, Real.exp_add]
        ring
      _ ≤ Real.exp (-step) * (terminalCard : ℝ) :=
        mul_le_mul_of_nonneg_left (by simpa [step] using hchain)
          (Real.exp_pos _).le
      _ ≤ (#B : ℝ) := by simpa [step] using hchild
  have hexp : Real.exp (-(1025 * (2 : ℝ) ^ 12 * K) * (d : ℝ) ^ 12) ≤
      Real.exp (-((n : ℝ) + 1) * step) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact (mul_le_mul_of_nonneg_right hexp (by positivity)).trans hcombined

/-- Assemble a raw analytic terminal certificate with the actual located
chain.  The output constant is explicit: `8` pays for density, while the two
child carriers each pay `257 * 2^12 * K`. -/
noncomputable def of_locatedTerminalData
    {N d n : ℕ} (hd : 1 ≤ d)
    {A : Finset (ZMod (intervalModulus N))} (hA : A.Nonempty)
    {K : ℝ} (hK : 0 ≤ K)
    {t : DensityStep.LocatedRestriction A}
    (hn : n ≤ 1024 * (d + 1))
    (hdyadic : BohrStopping.OnDyadicScale d
      (cyclicInitialLocated N A hA).density)
    (hdensity : (1025 / 1024 : ℝ) ^ n *
        (cyclicInitialLocated N A hA).density ≤ t.density)
    (hcard : Real.exp (-(n : ℝ) *
          (K * ((d + 1 : ℕ) : ℝ) ^ 11)) *
        ((cyclicInitialLocated N A hA).card : ℝ) ≤ (t.card : ℝ))
    (terminal : LocatedHolderTerminalData t K d) :
    CyclicHolderCertificate N A
      (8 + 2050 * (2 : ℝ) ^ 12 * K) d := by
  letI : NeZero (intervalModulus N) := ⟨by simp [intervalModulus]⟩
  let c := terminal.certificate
  have hinitNonneg : 0 ≤ (cyclicInitialLocated N A hA).density :=
    (cyclicInitialLocated N A hA).density_pos.le
  have hqpow : (1 : ℝ) ≤ (1025 / 1024 : ℝ) ^ n :=
    one_le_pow₀ (by norm_num)
  have hinit_le : (cyclicInitialLocated N A hA).density ≤ t.density := by
    calc
      (cyclicInitialLocated N A hA).density =
          1 * (cyclicInitialLocated N A hA).density := by ring
      _ ≤ (1025 / 1024 : ℝ) ^ n * (cyclicInitialLocated N A hA).density :=
        mul_le_mul_of_nonneg_right hqpow hinitNonneg
      _ ≤ t.density := hdensity
  have hscale : (1 / (2 : ℝ) ^ d) ≤
      (cyclicInitialLocated N A hA).density := hdyadic
  have halpha : (3 / 4 : ℝ) * (1 / (2 : ℝ) ^ d) ≤ c.alpha := by
    calc
      (3 / 4 : ℝ) * (1 / (2 : ℝ) ^ d) ≤
          (3 / 4 : ℝ) * (cyclicInitialLocated N A hA).density :=
        mul_le_mul_of_nonneg_left hscale (by norm_num)
      _ ≤ (3 / 4 : ℝ) * t.density :=
        mul_le_mul_of_nonneg_left hinit_le (by norm_num)
      _ ≤ c.alpha := terminal.alpha_lower
  have hdensityCube : Real.exp (-(8 : ℝ) * (d : ℝ) ^ 12) ≤
      c.alpha ^ 3 / 2 := density_cube_bound_of_dyadic hd halpha
  have hchainCard : Real.exp (-(n : ℝ) *
        (K * ((d + 1 : ℕ) : ℝ) ^ 11)) *
      (Fintype.card (ZMod (intervalModulus N)) : ℝ) ≤ (t.card : ℝ) := by
    simpa only [cyclicInitialLocated_card, ZMod.card] using hcard
  have hB : Real.exp (-(1025 * (2 : ℝ) ^ 12 * K) * (d : ℝ) ^ 12) *
      (Fintype.card (ZMod (intervalModulus N)) : ℝ) ≤ (#c.B : ℝ) := by
    exact child_card_bound_of_located_chain
      (G := ZMod (intervalModulus N)) (K := K) hK
      (d := d) (n := n) (terminalCard := t.card) hd hn hchainCard terminal.B_card
  have hB' : Real.exp (-(1025 * (2 : ℝ) ^ 12 * K) * (d : ℝ) ^ 12) *
      (Fintype.card (ZMod (intervalModulus N)) : ℝ) ≤ (#c.B' : ℝ) := by
    exact child_card_bound_of_located_chain
      (G := ZMod (intervalModulus N)) (K := K) hK
      (d := d) (n := n) (terminalCard := t.card) hd hn hchainCard terminal.B'_card
  have hbohr := bohr_product_of_individual_bounds hB hB'
  have hsize := quantitative_size_of_density_and_bohr hdensityCube hbohr
  exact ofHolderCountCertificate c (by
    convert hsize using 1 <;> ring)

end CyclicHolderCertificate

/-- The local maximal-state theorem implies concrete cyclic Holder
certificates.  This is the complete finite stopping and quantitative
bookkeeping assembly. -/
theorem holderCertificates_of_maximalTerminal
    {K : ℝ} (hterminal : KelleyMekaMaximalTerminalHypothesis K) :
    KelleyMekaHolderCertificateHypothesis
      (8 + 2050 * (2 : ℝ) ^ 12 * K) := by
  refine ⟨by
    have hcoef : (0 : ℝ) < 2050 * (2 : ℝ) ^ 12 := by positivity
    nlinarith [hterminal.1], ?_⟩
  intro N hN A hA d hd hlog
  obtain ⟨rankCost, hmaximal⟩ := hterminal.2 N hN A hA d hd hlog
  let sizeCost : ℝ := K * ((d + 1 : ℕ) : ℝ) ^ 11
  obtain ⟨n, hn, t, _hchain, hnoIncrement, hdensity, hrank, hcard⟩ :=
    exists_cyclic_fixedIncrement_maximalLocatedChain
      (rankCost := rankCost) hN hA hlog sizeCost
  have hdyadic := cyclicInitialLocated_onDyadicScale hN hA hlog
  have hterminalDensity : (1 / (2 : ℝ) ^ d) ≤ t.density := by
    calc
      (1 / (2 : ℝ) ^ d) ≤
          (cyclicInitialLocated N A hA).density := hdyadic
      _ = 1 * (cyclicInitialLocated N A hA).density := by rw [one_mul]
      _ ≤ (1025 / 1024 : ℝ) ^ n *
          (cyclicInitialLocated N A hA).density := by
        exact mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num))
          (cyclicInitialLocated N A hA).density_pos.le
      _ ≤ t.density := hdensity
  have hterminalRank : t.rank ≤ 1024 * (d + 1) * rankCost := by
    calc
      t.rank ≤ (cyclicInitialLocated N A hA).rank + n * rankCost := hrank
      _ = n * rankCost := by simp
      _ ≤ (1024 * (d + 1)) * rankCost := Nat.mul_le_mul_right rankCost hn
      _ = 1024 * (d + 1) * rankCost := rfl
  have hdata : Nonempty (LocatedHolderTerminalData t K d) := by
    apply hmaximal t
    · exact hterminalDensity
    · exact hterminalRank
    simpa [sizeCost] using hnoIncrement
  let data := Classical.choice hdata
  exact ⟨CyclicHolderCertificate.of_locatedTerminalData hd hA hterminal.1.le hn
    hdyadic hdensity (by simpa [sizeCost] using hcard) data⟩

/-- The reachable count-or-increment input implies the cyclic counting
theorem.  This is the formal bridge from the analytic one-step proposition to
the group-level statement consumed by `orderedCount_of_cyclic`. -/
theorem cyclicCount_of_reachableOneStep
    {K : ℝ} (hstep : KelleyMekaReachableOneStepHypothesis K) :
    KelleyMekaCyclicCountHypothesis (3 * (2 : ℝ) ^ 12 * K) := by
  refine ⟨mul_pos (mul_pos (by norm_num) (pow_pos (by norm_num) _)) hstep.1, ?_⟩
  intro N hN A hA d hd hlog
  obtain ⟨rankCost, hone⟩ := hstep.2 N hN A hA d hd hlog
  have hiter := ReachableIteration.count_lower_bound_twelfth hstep.1.le hone
    (cyclicInitial_density_nonneg A) (cyclicInitial_density_le_one hN A)
    (cyclicInitial_onDyadicScale hN hA hlog)
  have hp := add_one_pow_twelve_le hd
  have hcost :
      DensityIteration.twelfthPowerCost K d ≤
        (3 * (2 : ℝ) ^ 12 * K) * (d : ℝ) ^ 12 := by
    calc
      DensityIteration.twelfthPowerCost K d =
          3 * K * ((d + 1 : ℕ) : ℝ) ^ 12 := rfl
      _ ≤ 3 * K * ((2 : ℝ) ^ 12 * (d : ℝ) ^ 12) :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num) hstep.1.le)
      _ = (3 * (2 : ℝ) ^ 12 * K) * (d : ℝ) ^ 12 := by ring
  have hexp :
      Real.exp (-(3 * (2 : ℝ) ^ 12 * K) * (d : ℝ) ^ 12) ≤
        Real.exp (-(DensityIteration.twelfthPowerCost K d)) := by
    apply Real.exp_le_exp.mpr
    calc
      -(3 * (2 : ℝ) ^ 12 * K) * (d : ℝ) ^ 12 =
          -((3 * (2 : ℝ) ^ 12 * K) * (d : ℝ) ^ 12) := by ring
      _ ≤ -(DensityIteration.twelfthPowerCost K d) := neg_le_neg hcost
  exact (mul_le_mul_of_nonneg_right hexp
    (sq_nonneg (((intervalModulus N : ℕ) : ℝ)))).trans (by
      simpa [DensityIteration.HasCount, cyclicInitialState] using hiter)

private lemma intervalModulus_cast_le_four_mul {N : ℕ} (hN : 1 ≤ N) :
    (((intervalModulus N : ℕ) : ℝ)) ≤ 4 * (N : ℝ) := by
  push_cast
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

private lemma log_intervalModulus_div_card_le
    {N d : ℕ} {A : Finset ℕ} (hN : 1 ≤ N) (hA : A.Nonempty)
    (hlog : Real.log ((N : ℝ) / (#A : ℝ)) ≤ (d : ℝ) * Real.log 2) :
    Real.log (((intervalModulus N : ℕ) : ℝ) / (#A : ℝ)) ≤
      ((d + 2 : ℕ) : ℝ) * Real.log 2 := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hAreal : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
  have hratioN : (0 : ℝ) < (N : ℝ) / (#A : ℝ) := div_pos hNreal hAreal
  have hratio_le :
      (((intervalModulus N : ℕ) : ℝ) / (#A : ℝ)) ≤
        4 * ((N : ℝ) / (#A : ℝ)) := by
    calc
      (((intervalModulus N : ℕ) : ℝ) / (#A : ℝ)) ≤
          (4 * (N : ℝ)) / (#A : ℝ) :=
        div_le_div_of_nonneg_right (intervalModulus_cast_le_four_mul hN) hAreal.le
      _ = 4 * ((N : ℝ) / (#A : ℝ)) := by ring
  calc
    Real.log (((intervalModulus N : ℕ) : ℝ) / (#A : ℝ)) ≤
        Real.log (4 * ((N : ℝ) / (#A : ℝ))) :=
      Real.log_le_log (by positivity) hratio_le
    _ = 2 * Real.log 2 + Real.log ((N : ℝ) / (#A : ℝ)) := by
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hratioN.ne',
        show (4 : ℝ) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    _ ≤ 2 * Real.log 2 + (d : ℝ) * Real.log 2 := by linarith
    _ = ((d + 2 : ℕ) : ℝ) * Real.log 2 := by
      push_cast
      ring

private lemma add_two_pow_twelve_le {d : ℕ} (hd : 1 ≤ d) :
    ((d + 2 : ℕ) : ℝ) ^ 12 ≤ (3 : ℝ) ^ 12 * (d : ℝ) ^ 12 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hbase : ((d + 2 : ℕ) : ℝ) ≤ 3 * (d : ℝ) := by
    push_cast
    linarith
  calc
    ((d + 2 : ℕ) : ℝ) ^ 12 ≤ (3 * (d : ℝ)) ^ 12 :=
      pow_le_pow_left₀ (by positivity) hbase 12
    _ = (3 : ℝ) ^ 12 * (d : ℝ) ^ 12 := by rw [mul_pow]

/-- The cyclic Kelley--Meka estimate implies the interval estimate.  The
harmless factor `3^12` absorbs both the change from `N` to `2*N+1` and the
two extra dyadic density units (`2*N+1 <= 4*N`). -/
theorem orderedCount_of_cyclic
    {K : ℝ} (hcyclic : KelleyMekaCyclicCountHypothesis K) :
    KelleyMekaOrderedCountHypothesis ((3 : ℝ) ^ 12 * K) 1 := by
  refine ⟨mul_pos (pow_pos (by norm_num) _) hcyclic.1, ?_⟩
  intro N hN A hAIcc hA d hd hlog
  have hAle : ∀ a ∈ A, a ≤ N := by
    intro a ha
    exact (Finset.mem_Icc.mp (hAIcc ha)).2
  have hImageNonempty : (intervalImage N A).Nonempty := by
    obtain ⟨a, ha⟩ := hA
    exact ⟨intervalEmbedding N a, mem_intervalImage.mpr ⟨a, ha, rfl⟩⟩
  have hImageCard : #(intervalImage N A) = #A := card_intervalImage hAle
  have hgroupLog :
      Real.log (((intervalModulus N : ℕ) : ℝ) /
          (#(intervalImage N A) : ℝ)) ≤
        ((d + 2 : ℕ) : ℝ) * Real.log 2 := by
    rw [hImageCard]
    exact log_intervalModulus_div_card_le hN hA hlog
  have hgroup := hcyclic.2 N hN (intervalImage N A) hImageNonempty
    (d + 2) (by omega) hgroupLog
  have hpow := add_two_pow_twelve_le hd
  have hexp :
      Real.exp (-((3 : ℝ) ^ 12 * K) * (d : ℝ) ^ 12) ≤
        Real.exp (-K * ((d + 2 : ℕ) : ℝ) ^ 12) := by
    apply Real.exp_le_exp.mpr
    have hK := hcyclic.1.le
    nlinarith [mul_le_mul_of_nonneg_left hpow hK]
  have hNcard : (N : ℝ) ^ 2 ≤ (((intervalModulus N : ℕ) : ℝ)) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) _ 2
    push_cast
    have hN0 : (0 : ℝ) ≤ N := by positivity
    linarith
  calc
    Real.exp (-((3 : ℝ) ^ 12 * K) * (d : ℝ) ^ 12) * (N : ℝ) ^ 2 ≤
        Real.exp (-K * ((d + 2 : ℕ) : ℝ) ^ 12) *
          (((intervalModulus N : ℕ) : ℝ)) ^ 2 :=
      mul_le_mul hexp hNcard (sq_nonneg _) (Real.exp_pos _).le
    _ ≤ (threeAPCount (intervalImage N A) : ℝ) := hgroup
    _ = (threeAPCount A : ℝ) := by rw [threeAPCount_intervalImage hAle]

/-- Existential form of `orderedCount_of_cyclic`, used by the public theorem.
The only remaining input after this lemma is the unconditional cyclic-group
counting theorem supplied by the analytic density iteration. -/
theorem exists_orderedCount_of_exists_cyclic
    (h : ∃ K : ℝ, KelleyMekaCyclicCountHypothesis K) :
    ∃ K : ℝ, ∃ N₀ : ℕ, KelleyMekaOrderedCountHypothesis K N₀ := by
  obtain ⟨K, hK⟩ := h
  exact ⟨(3 : ℝ) ^ 12 * K, 1, orderedCount_of_cyclic hK⟩

/-- Full quantitative bookkeeping from a proved reachable one-step theorem to
the exact ordered interval-count hypothesis used by `Quantitative.lean`. -/
theorem exists_orderedCount_of_exists_reachableOneStep
    (h : ∃ K : ℝ, KelleyMekaReachableOneStepHypothesis K) :
    ∃ K : ℝ, ∃ N₀ : ℕ, KelleyMekaOrderedCountHypothesis K N₀ := by
  obtain ⟨K, hK⟩ := h
  exact exists_orderedCount_of_exists_cyclic
    ⟨3 * (2 : ℝ) ^ 12 * K, cyclicCount_of_reachableOneStep hK⟩

/-- Full assembly from concrete balanced/Hölder certificates to the ordered
interval hypothesis. -/
theorem exists_orderedCount_of_exists_holderCertificates
    (h : ∃ K : ℝ, KelleyMekaHolderCertificateHypothesis K) :
    ∃ K : ℝ, ∃ N₀ : ℕ, KelleyMekaOrderedCountHypothesis K N₀ := by
  obtain ⟨K, hK⟩ := h
  exact exists_orderedCount_of_exists_cyclic
    ⟨K, cyclicCount_of_holderCertificates hK⟩

/-- Full assembly from the fixed-state maximal located analytic theorem to
the ordered interval count. -/
theorem exists_orderedCount_of_exists_maximalTerminal
    (h : ∃ K : ℝ, KelleyMekaMaximalTerminalHypothesis K) :
    ∃ K : ℝ, ∃ N₀ : ℕ, KelleyMekaOrderedCountHypothesis K N₀ := by
  obtain ⟨K, hK⟩ := h
  exact exists_orderedCount_of_exists_holderCertificates
    ⟨8 + 2050 * (2 : ℝ) ^ 12 * K,
      holderCertificates_of_maximalTerminal hK⟩

/-- Final central composition from the conclusion exposed by the analytic
density-step module to the exact ordered Kelley--Meka count theorem. -/
theorem exists_orderedCount_of_exists_terminalProducer
    (h : ∃ K : ℝ, KelleyMekaTerminalProducerHypothesis K) :
    ∃ K : ℝ, ∃ N₀ : ℕ, KelleyMekaOrderedCountHypothesis K N₀ := by
  obtain ⟨K, hK⟩ := h
  exact exists_orderedCount_of_exists_maximalTerminal
    ⟨K, maximalTerminal_of_terminalProducer hK⟩

#print axioms orderedCount_of_cyclic
#print axioms exists_orderedCount_of_exists_cyclic
#print axioms cyclicCount_of_reachableOneStep
#print axioms exists_orderedCount_of_exists_reachableOneStep
#print axioms cyclicCount_of_holderCertificates
#print axioms exists_orderedCount_of_exists_holderCertificates
#print axioms exists_maximalLocatedChain
#print axioms exists_cyclic_fixedIncrement_maximalLocatedChain
#print axioms LocatedHolderTerminalData.ofDensePair
#print axioms maximalTerminal_of_terminalProducer
#print axioms holderCertificates_of_maximalTerminal
#print axioms exists_orderedCount_of_exists_maximalTerminal
#print axioms exists_orderedCount_of_exists_terminalProducer

end Erdos140
