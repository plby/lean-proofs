/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos297.WeightedFourier
import ErdosProblems.Erdos297.GoodFactorization
import ErdosProblems.Erdos297.NearbyMultiple
import ErdosProblems.Erdos297.ActiveLcm
import ErdosProblems.Erdos297.MajorEventual
import ErdosProblems.Erdos297.MinorEventual
import ErdosProblems.Erdos297.EntropyTypical
import ErdosProblems.Erdos297.FiniteHoeffding

/-!
# The finite local-limit assembly for Erdős Problem 297

This file isolates the last, exact, finite step in Liu--Sawhney's local-limit
argument.  The Fourier estimates first put mass at least `1 / (2 Q)` on the
event that the cleared reciprocal sum has the prescribed value modulo `Q`.
The bounded-difference estimate then shows that nonzero integral translates
have total mass at most `1 / (4 Q)`.  Subtraction leaves `1 / (4 Q)` on the
single desired value.

The analytic and arithmetic work needed to establish the two estimates is
kept visible in the hypotheses of `liuSawhney_local_limit`: no asymptotic
notation or probability-space coercions occur in this finite assembly.
-/

open scoped BigOperators

namespace Erdos297.LocalLimit

open Finset
open Erdos297.WeightedFourier
open Erdos297.GoodFactorization
open Erdos297.ActiveLcm
open Erdos297.EntropyTypical
open Erdos297.FiniteHoeffding
open Filter

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Bernoulli mass of the subsets whose natural-valued additive statistic is
exactly `target`. -/
def exactBernoulliMass {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (step : ι → ℕ) (p : ι → ℝ) (target : ℕ) : ℝ :=
  ∑ B ∈ I.powerset,
    if B.sum step = target then subsetWeight I p B else 0

/-- Bernoulli mass outside the closed interval of radius `Q - 1` about the
target.  Thus every nonzero value congruent to `target` modulo `Q` belongs to
this event. -/
def offLatticeMass {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (step : ι → ℕ) (p : ι → ℝ)
    (target Q : ℕ) : ℝ :=
  ∑ B ∈ I.powerset,
    if Q ≤ Int.natAbs (((B.sum step : ℕ) : ℤ) - (target : ℤ)) then
      subsetWeight I p B
    else 0

/-- Contribution of a finite block of Fourier frequencies before the global
factor `1 / Q` is applied. -/
def fourierBlock {ι : Type*} [DecidableEq ι] {Q : ℕ} [NeZero Q]
    (frequencies : Finset (ZMod Q)) (I : Finset ι)
    (step : ι → ZMod Q) (p : ι → ℝ) (target : ZMod Q) : ℂ :=
  ∑ h ∈ frequencies,
    ZMod.stdAddChar (h * target) * coefficient I step p h

/-- Splitting the nonzero frequencies into disjoint major and minor blocks
splits the Fourier error literally. -/
lemma nonzeroError_eq_fourierBlock_add
    {ι : Type*} [DecidableEq ι] {Q : ℕ} [NeZero Q]
    (major minor : Finset (ZMod Q))
    (I : Finset ι) (step : ι → ZMod Q) (p : ι → ℝ) (target : ZMod Q)
    (hdisjoint : Disjoint major minor)
    (hcover : major ∪ minor = (Finset.univ.erase 0 : Finset (ZMod Q))) :
    nonzeroError Q I step p target =
      fourierBlock major I step p target +
        fourierBlock minor I step p target := by
  rw [nonzeroError, ← hcover, Finset.sum_union hdisjoint]
  simp only [fourierBlock]

/-- Source-form major/minor assembly.  The major block (including the zero
mode, written separately as `1`) contributes at least `3/4`, while the minor
block costs at most `1/4`; hence the prescribed congruence class has mass at
least `1/(2Q)`. -/
theorem residueMass_lower_bound_of_major_minor
    {ι : Type*} [DecidableEq ι] {Q : ℕ} [NeZero Q]
    (major minor : Finset (ZMod Q))
    (I : Finset ι) (step : ι → ZMod Q) (p : ι → ℝ) (target : ZMod Q)
    (hdisjoint : Disjoint major minor)
    (hcover : major ∪ minor = (Finset.univ.erase 0 : Finset (ZMod Q)))
    (hmajor : 3 / 4 ≤ 1 + (fourierBlock major I step p target).re)
    (hminor : ‖fourierBlock minor I step p target‖ ≤ 1 / 4) :
    1 / (2 * (Q : ℝ)) ≤ residueMass Q I step p target := by
  have hsplit := nonzeroError_eq_fourierBlock_add
    major minor I step p target hdisjoint hcover
  have hminorRe : -(1 / 4 : ℝ) ≤
      (fourierBlock minor I step p target).re := by
    have habs : |(fourierBlock minor I step p target).re| ≤ 1 / 4 :=
      (Complex.abs_re_le_norm _).trans hminor
    exact (abs_le.mp habs).1
  have hscaled := modulus_mul_residueMass_eq I step p target
  have hQ : 0 < (Q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  rw [hsplit, Complex.add_re] at hscaled
  have hhalf : (1 / 2 : ℝ) ≤
      (Q : ℝ) * residueMass Q I step p target := by
    nlinarith
  calc
    1 / (2 * (Q : ℝ)) = (1 / 2 : ℝ) / Q := by field_simp
    _ ≤ residueMass Q I step p target :=
      (div_le_iff₀ hQ).2 (by simpa [mul_comm] using hhalf)

/-- The product notation used by `WeightedFourier` is the usual coordinatewise
Bernoulli weight on every subset of the ambient set. -/
lemma subsetWeight_eq_bernoulliWeight {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (p : ι → ℝ) {B : Finset ι} (hB : B ⊆ I) :
    subsetWeight I p B = Erdos297.EntropyTypical.bernoulliWeight I p B := by
  rw [subsetWeight, Erdos297.EntropyTypical.bernoulliWeight, Finset.prod_ite]
  have hfilter : I.filter (fun i ↦ i ∈ B) = B := by
    ext i
    simp [and_iff_right_of_imp (fun hi ↦ hB hi)]
  have hfilterNot : I.filter (fun i ↦ i ∉ B) = I \ B := by
    ext i
    simp [and_comm]
  rw [hfilter, hfilterNot]

/-- `exactBernoulliMass` may equivalently be written with the Bernoulli weight
used by the entropy/typical-set development. -/
theorem exactBernoulliMass_eq_sum_bernoulliWeight
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (step : ι → ℕ) (p : ι → ℝ) (target : ℕ) :
    exactBernoulliMass I step p target =
      ∑ B ∈ I.powerset,
        if B.sum step = target then
          Erdos297.EntropyTypical.bernoulliWeight I p B else 0 := by
  apply Finset.sum_congr rfl
  intro B hB
  rw [subsetWeight_eq_bernoulliWeight I p (Finset.mem_powerset.mp hB)]

/-- Integer congruence modulo a positive modulus forces a nonzero difference
to have absolute value at least that modulus. -/
lemma modulus_le_natAbs_sub_of_zmod_eq_of_ne
    {Q u v : ℕ} [NeZero Q]
    (hmod : (u : ZMod Q) = v) (hne : u ≠ v) :
    Q ≤ Int.natAbs ((u : ℤ) - v) := by
  have hdvd : (Q : ℤ) ∣ (u : ℤ) - v := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast sub_eq_zero.mpr hmod
  have hsub : (u : ℤ) - v ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  simpa using Int.natAbs_le_of_dvd_ne_zero hdvd hsub

/-- The mass in one residue class is at most the exact atom plus the mass of
the off-lattice tail. -/
theorem residueMass_le_exact_add_offLattice
    {ι : Type*} [DecidableEq ι] {Q : ℕ} [NeZero Q]
    (I : Finset ι) (step : ι → ℕ) (p : ι → ℝ) (target : ℕ)
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1) :
    residueMass Q I (fun i ↦ (step i : ZMod Q)) p target ≤
      exactBernoulliMass I step p target +
        offLatticeMass I step p target Q := by
  unfold residueMass exactBernoulliMass offLatticeMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro B hB
  have hw : 0 ≤ subsetWeight I p B :=
    subsetWeight_nonneg I p hp0 hp1 hB
  by_cases heq : B.sum step = target
  · have hmod : B.sum (fun i ↦ (step i : ZMod Q)) =
        (target : ZMod Q) := by
      rw [← heq]
      norm_cast
    have hQne : Q ≠ 0 := NeZero.ne Q
    simp [heq, hmod, hQne, hw]
  · have hcastSum : B.sum (fun i ↦ (step i : ZMod Q)) =
        ((B.sum step : ℕ) : ZMod Q) := by
      norm_cast
    by_cases hmod : B.sum (fun i ↦ (step i : ZMod Q)) = target
    · have hmod' : ((B.sum step : ℕ) : ZMod Q) = (target : ZMod Q) := by
        rw [← hcastSum]
        exact hmod
      have hfar : Q ≤ Int.natAbs (((B.sum step : ℕ) : ℤ) - target) :=
        modulus_le_natAbs_sub_of_zmod_eq_of_ne
          hmod' heq
      have hfar' : Q ≤
          Int.natAbs ((∑ i ∈ B, (step i : ℤ)) - (target : ℤ)) := by
        simpa only [Nat.cast_sum] using hfar
      simp [heq, hmod, hfar', hw]
    · simp only [Nat.cast_sum, ge_iff_le]
      split_ifs <;> positivity

/-- The integer off-lattice event is the ordinary real tail of the cleared
subset sum. -/
theorem offLatticeMass_le_eventMass
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (step : ι → ℕ) (p : ι → ℝ) (target Q : ℕ)
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1) :
    offLatticeMass I step p target Q ≤
      eventMass I p (fun B ↦
        (Q : ℝ) ≤
          |subsetSum B (fun i ↦ (step i : ℝ)) - (target : ℝ)|) := by
  unfold offLatticeMass eventMass
  apply Finset.sum_le_sum
  intro B hB
  have hw : 0 ≤ subsetWeight I p B :=
    subsetWeight_nonneg I p hp0 hp1 hB
  by_cases hfar : Q ≤
      Int.natAbs (((B.sum step : ℕ) : ℤ) - (target : ℤ))
  · have hfarZ : (Q : ℤ) ≤
        |((B.sum step : ℕ) : ℤ) - (target : ℤ)| := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hfar
    have hfarR : (Q : ℝ) ≤
        |((B.sum step : ℕ) : ℝ) - (target : ℝ)| := by
      exact_mod_cast hfarZ
    have hsum : subsetSum B (fun i ↦ (step i : ℝ)) =
        ((B.sum step : ℕ) : ℝ) := by
      simp only [Erdos297.FiniteHoeffding.subsetSum]
      norm_cast
    have htail : (Q : ℝ) ≤
        |subsetSum B (fun i ↦ (step i : ℝ)) - (target : ℝ)| := by
      simpa only [hsum] using hfarR
    simp only [hfar, htail, if_true]
    exact le_rfl
  · rw [if_neg hfar]
    exact ite_nonneg hw le_rfl

/-- Hoeffding supplies the off-lattice estimate from exact centering of the
cleared integer statistic. -/
theorem offLatticeMass_le_hoeffding
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (step : ι → ℕ) (p : ι → ℝ) (target Q : ℕ)
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1)
    (hmean : subsetMean I p (fun i ↦ (step i : ℝ)) = target) :
    offLatticeMass I step p target Q ≤
      2 * Real.exp (-((Q : ℝ) ^ 2) /
        (2 * squareSum I (fun i ↦ (step i : ℝ)))) := by
  refine (offLatticeMass_le_eventMass I step p target Q hp0 hp1).trans ?_
  have htail := abs_subsetSum_sub_mean_tail I p
    (fun i ↦ (step i : ℝ)) hp0 hp1 (t := (Q : ℝ)) (by positivity)
  simpa only [hmean] using htail

/-- Exact denominator clearing for an arbitrary positive common multiple.
This is the form needed for the active LCM of the sampled denominator set. -/
lemma commonMultiple_mul_recSum
    {Q : ℕ} {B : Finset ℕ} (hB0 : 0 ∉ B)
    (hdiv : ∀ n ∈ B, n ∣ Q) :
    (Q : ℚ) * UnitFractions.rec_sum B =
      ∑ n ∈ B, ((Q / n : ℕ) : ℚ) := by
  rw [UnitFractions.rec_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := fun hnzero ↦ hB0 (hnzero ▸ hn)
  field_simp [hn0]
  exact_mod_cast (by
    simpa [Nat.mul_comm] using (Nat.div_mul_cancel (hdiv n hn)).symm)

/-- For denominators dividing a positive common multiple `Q`, a cleared-sum
displacement of at least `Q` is a reciprocal-sum displacement of at least
one.  In particular this applies to the active LCM, without introducing the
spurious repeated zero modes caused by a larger ambient modulus. -/
theorem offLatticeMass_le_reciprocalEventMass_of_commonMultiple
    {Q z : ℕ} (hQ : 0 < Q)
    (I : Finset ℕ) (hIpos : ∀ n ∈ I, 0 < n)
    (hIdiv : ∀ n ∈ I, n ∣ Q)
    (p : ℕ → ℝ)
    (hp0 : ∀ n ∈ I, 0 ≤ p n) (hp1 : ∀ n ∈ I, p n ≤ 1) :
    offLatticeMass I (fun n ↦ Q / n) p z Q ≤
      eventMass I p (fun B ↦
        1 ≤ |subsetSum B (fun n : ℕ ↦ (n : ℝ)⁻¹) -
          (z : ℝ) / (Q : ℝ)|) := by
  unfold offLatticeMass eventMass
  apply Finset.sum_le_sum
  intro B hB
  have hBsub : B ⊆ I := Finset.mem_powerset.mp hB
  have hw : 0 ≤ subsetWeight I p B :=
    subsetWeight_nonneg I p hp0 hp1 hB
  have hQreal : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hcleared :
      (Q : ℝ) *
          subsetSum B (fun n : ℕ ↦ (n : ℝ)⁻¹) =
        ((B.sum (fun n ↦ Q / n) : ℕ) : ℝ) := by
    simp only [Erdos297.FiniteHoeffding.subsetSum]
    rw [Finset.mul_sum]
    calc
      (∑ n ∈ B, (Q : ℝ) * (n : ℝ)⁻¹) =
          ∑ n ∈ B, ((Q / n : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnpos := hIpos n (hBsub hn)
        have hndvd := hIdiv n (hBsub hn)
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
        rw [inv_eq_one_div, mul_one_div]
        apply (div_eq_iff hn0).2
        norm_cast
        simpa [Nat.mul_comm] using (Nat.div_mul_cancel hndvd).symm
      _ = ((B.sum (fun n ↦ Q / n) : ℕ) : ℝ) := by
        norm_cast
  by_cases hfar : Q ≤ Int.natAbs
      (((B.sum (fun n ↦ Q / n) : ℕ) : ℤ) - (z : ℤ))
  · have hfarZ : (Q : ℤ) ≤
        |((B.sum (fun n ↦ Q / n) : ℕ) : ℤ) - (z : ℤ)| := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hfar
    have hfarR : (Q : ℝ) ≤
        |((B.sum (fun n ↦ Q / n) : ℕ) : ℝ) - (z : ℝ)| := by
      exact_mod_cast hfarZ
    have hdiff :
        subsetSum B (fun n : ℕ ↦ (n : ℝ)⁻¹) -
            (z : ℝ) / (Q : ℝ) =
          (((B.sum (fun n ↦ Q / n) : ℕ) : ℝ) - z) / (Q : ℝ) := by
      apply (eq_div_iff hQreal.ne').2
      rw [sub_mul, mul_comm
        (subsetSum B (fun n : ℕ ↦ (n : ℝ)⁻¹)) (Q : ℝ), hcleared]
      field_simp [hQreal.ne']
    have htail : 1 ≤
        |subsetSum B (fun n : ℕ ↦ (n : ℝ)⁻¹) -
          (z : ℝ) / (Q : ℝ)| := by
      rw [hdiff, abs_div, abs_of_pos hQreal, one_le_div hQreal]
      exact hfarR
    simp only [hfar, htail, if_true]
    exact le_rfl
  · rw [if_neg hfar]
    exact ite_nonneg hw le_rfl

/-- Smooth-LCM specialization of the common-multiple tail bridge. -/
theorem offLatticeMass_le_reciprocalEventMass
    {N M S z : ℕ} (hM : 1 ≤ M)
    (I : Finset ℕ) (hI : I ⊆ goodDenominators N M S)
    (p : ℕ → ℝ)
    (hp0 : ∀ n ∈ I, 0 ≤ p n) (hp1 : ∀ n ∈ I, p n ≤ 1) :
    offLatticeMass I (fun n ↦ smoothLcm S / n) p z (smoothLcm S) ≤
      eventMass I p (fun B ↦
        1 ≤ |subsetSum B (fun n : ℕ ↦ (n : ℝ)⁻¹) -
          (z : ℝ) / (smoothLcm S : ℝ)|) := by
  apply offLatticeMass_le_reciprocalEventMass_of_commonMultiple
    (Q := smoothLcm S) (z := z)
  · exact Nat.pos_of_ne_zero (by
      simp [smoothLcm, Erdos285.PrimePowers.initialLcm])
  · intro n hn
    exact goodDenominator_pos hM (hI hn)
  · intro n hn
    exact goodDenominator_dvd_smoothLcm hM (hI hn)
  · exact hp0
  · exact hp1

/-- Reciprocal Hoeffding tail in the exact form consumed by the local-limit
assembly. -/
theorem offLatticeMass_le_reciprocal_hoeffding
    {N M S z : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N)
    (I : Finset ℕ) (hI : I ⊆ goodDenominators N M S)
    (p : ℕ → ℝ)
    (hp0 : ∀ n ∈ I, 0 ≤ p n) (hp1 : ∀ n ∈ I, p n ≤ 1)
    (hmean : subsetMean I p (fun n : ℕ ↦ (n : ℝ)⁻¹) =
      (z : ℝ) / (smoothLcm S : ℝ)) :
    offLatticeMass I (fun n ↦ smoothLcm S / n) p z (smoothLcm S) ≤
      2 * Real.exp (-((M : ℝ) ^ 2) / (2 * (N : ℝ))) := by
  refine (offLatticeMass_le_reciprocalEventMass hM I hI p hp0 hp1).trans ?_
  have hIcc : I ⊆ Finset.Icc M N :=
    hI.trans (goodDenominators_subset_Icc N M S)
  have htail := abs_reciprocal_sum_sub_mean_tail p
    (Nat.lt_of_lt_of_le Nat.zero_lt_one hM) hMN hIcc hp0 hp1
  simpa only [hmean] using htail

/-- Finite local-limit assembly.  A half-unit Fourier error gives mass
`1/(2Q)` in the desired congruence class; an off-lattice tail of size at most
`1/(4Q)` leaves the claimed atom.  This is the final subtraction in
Liu--Sawhney Proposition 3.2. -/
theorem liuSawhney_local_limit
    {ι : Type*} [DecidableEq ι] {Q : ℕ} [NeZero Q]
    (I : Finset ι) (step : ι → ℕ) (p : ι → ℝ) (target : ℕ)
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1)
    (hfourier :
      ‖nonzeroError Q I (fun i ↦ (step i : ZMod Q)) p target‖ ≤ 1 / 2)
    (htail : offLatticeMass I step p target Q ≤ 1 / (4 * (Q : ℝ))) :
    1 / (4 * (Q : ℝ)) ≤ exactBernoulliMass I step p target := by
  have hresidue : 1 / (2 * (Q : ℝ)) ≤
      residueMass Q I (fun i ↦ (step i : ZMod Q)) p target := by
    have h := residueMass_lower_bound_of_error_norm
      I (fun i ↦ (step i : ZMod Q)) p (target : ZMod Q) hfourier
    convert h using 1 <;> ring
  have hpartition := residueMass_le_exact_add_offLattice
    (Q := Q) I step p target hp0 hp1
  have hscale : 1 / (2 * (Q : ℝ)) =
      2 * (1 / (4 * (Q : ℝ))) := by
    have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne Q)
    field_simp
    norm_num
  linarith

/-- The same finite local limit in the source's major/minor-arc form. -/
theorem liuSawhney_local_limit_of_major_minor
    {ι : Type*} [DecidableEq ι] {Q : ℕ} [NeZero Q]
    (major minor : Finset (ZMod Q))
    (I : Finset ι) (step : ι → ℕ) (p : ι → ℝ) (target : ℕ)
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1)
    (hdisjoint : Disjoint major minor)
    (hcover : major ∪ minor = (Finset.univ.erase 0 : Finset (ZMod Q)))
    (hmajor : 3 / 4 ≤ 1 +
      (fourierBlock major I (fun i ↦ (step i : ZMod Q)) p target).re)
    (hminor :
      ‖fourierBlock minor I (fun i ↦ (step i : ZMod Q)) p target‖ ≤ 1 / 4)
    (htail : offLatticeMass I step p target Q ≤ 1 / (4 * (Q : ℝ))) :
    1 / (4 * (Q : ℝ)) ≤ exactBernoulliMass I step p target := by
  have hresidue := residueMass_lower_bound_of_major_minor major minor I
    (fun i ↦ (step i : ZMod Q)) p (target : ZMod Q)
    hdisjoint hcover hmajor hminor
  have hpartition := residueMass_le_exact_add_offLattice
    (Q := Q) I step p target hp0 hp1
  have hscale : 1 / (2 * (Q : ℝ)) =
      2 * (1 / (4 * (Q : ℝ))) := by
    have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne Q)
    field_simp
    norm_num
  linarith

/-- Fully analytic finite version: the off-lattice hypothesis is discharged
by finite Hoeffding, leaving only the explicit numerical comparison with
`1/(4Q)`. -/
theorem liuSawhney_local_limit_of_major_minor_hoeffding
    {ι : Type*} [DecidableEq ι] {Q : ℕ} [NeZero Q]
    (major minor : Finset (ZMod Q))
    (I : Finset ι) (step : ι → ℕ) (p : ι → ℝ) (target : ℕ)
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1)
    (hmean : subsetMean I p (fun i ↦ (step i : ℝ)) = target)
    (hdisjoint : Disjoint major minor)
    (hcover : major ∪ minor = (Finset.univ.erase 0 : Finset (ZMod Q)))
    (hmajor : 3 / 4 ≤ 1 +
      (fourierBlock major I (fun i ↦ (step i : ZMod Q)) p target).re)
    (hminor :
      ‖fourierBlock minor I (fun i ↦ (step i : ZMod Q)) p target‖ ≤ 1 / 4)
    (hTailNumeric :
      2 * Real.exp (-((Q : ℝ) ^ 2) /
        (2 * squareSum I (fun i ↦ (step i : ℝ)))) ≤
          1 / (4 * (Q : ℝ))) :
    1 / (4 * (Q : ℝ)) ≤ exactBernoulliMass I step p target := by
  apply liuSawhney_local_limit_of_major_minor major minor I step p target
    hp0 hp1 hdisjoint hcover hmajor hminor
  exact (offLatticeMass_le_hoeffding I step p target Q hp0 hp1 hmean).trans
    hTailNumeric

/-! ## Reciprocal-sum specialization -/

/-- Exact Bernoulli mass of a rational reciprocal-sum event. -/
def exactReciprocalMass (I : Finset ℕ) (p : ℕ → ℝ) (r : ℚ) : ℝ :=
  ∑ B ∈ I.powerset,
    if UnitFractions.rec_sum B = r then
      Erdos297.EntropyTypical.bernoulliWeight I p B else 0

/-- If every active denominator divides `Q`, clearing by `Q` identifies the
exact reciprocal-sum event with an exact natural subset-sum event. -/
theorem exactBernoulliMass_commonMultiple_eq_exactReciprocalMass
    {Q z : ℕ} (hQ : 0 < Q)
    (I : Finset ℕ) (hIpos : ∀ n ∈ I, 0 < n)
    (hIdiv : ∀ n ∈ I, n ∣ Q) (p : ℕ → ℝ) :
    exactBernoulliMass I (fun n ↦ Q / n) p z =
      exactReciprocalMass I p (z / (Q : ℚ)) := by
  rw [exactBernoulliMass_eq_sum_bernoulliWeight]
  unfold exactReciprocalMass
  apply Finset.sum_congr rfl
  intro B hB
  have hBI : B ⊆ I := Finset.mem_powerset.mp hB
  have hB0 : 0 ∉ B := by
    intro hzero
    exact (Nat.not_lt_zero 0) (hIpos 0 (hBI hzero))
  have hclear := commonMultiple_mul_recSum hB0
    (fun n hn ↦ hIdiv n (hBI hn))
  have hevent :
      B.sum (fun n ↦ Q / n) = z ↔
        UnitFractions.rec_sum B = z / (Q : ℚ) := by
    constructor
    · intro hsum
      have hcastsum :
          ((B.sum (fun n ↦ Q / n) : ℕ) : ℚ) = z := by
        exact_mod_cast hsum
      have hq : (Q : ℚ) * UnitFractions.rec_sum B = z := by
        calc
          (Q : ℚ) * UnitFractions.rec_sum B =
              ∑ n ∈ B, ((Q / n : ℕ) : ℚ) := hclear
          _ = ((B.sum (fun n ↦ Q / n) : ℕ) : ℚ) := by
            push_cast
            rfl
          _ = z := hcastsum
      apply (eq_div_iff (by exact_mod_cast hQ.ne')).2
      simpa [mul_comm] using hq
    · intro hrec
      have hq : (Q : ℚ) * UnitFractions.rec_sum B = z := by
        rw [hrec]
        field_simp
      have hcast :
          ((B.sum (fun n ↦ Q / n) : ℕ) : ℚ) = z := by
        calc
          ((B.sum (fun n ↦ Q / n) : ℕ) : ℚ) =
              ∑ n ∈ B, ((Q / n : ℕ) : ℚ) := by
            push_cast
            rfl
          _ = (Q : ℚ) * UnitFractions.rec_sum B := hclear.symm
          _ = z := hq
      exact_mod_cast hcast
  simp only [hevent]

/-- Clearing the common smooth denominator identifies exact reciprocal sums
with exact natural subset sums. -/
theorem exactBernoulliMass_smoothLcm_eq_exactReciprocalMass
    {N M S z : ℕ} (hM : 1 ≤ M)
    (I : Finset ℕ) (hI : I ⊆ goodDenominators N M S)
    (p : ℕ → ℝ) :
    exactBernoulliMass I (fun n ↦ smoothLcm S / n) p z =
      exactReciprocalMass I p (z / (smoothLcm S : ℚ)) := by
  have hQpos : 0 < smoothLcm S := Nat.pos_of_ne_zero (by
    simp [smoothLcm, Erdos285.PrimePowers.initialLcm])
  apply exactBernoulliMass_commonMultiple_eq_exactReciprocalMass hQpos I
  · intro n hn
    exact goodDenominator_pos hM (hI hn)
  · intro n hn
    exact goodDenominator_dvd_smoothLcm hM (hI hn)

/-- Source-faithful finite form of Liu--Sawhney Proposition 3.2.  The modulus
is a positive common multiple of the *active* denominators; in the concrete
application it is their LCM.  Using a larger ambient smooth LCM here would
introduce repeated zero modes into the Fourier expansion. -/
theorem liuSawhney_proposition_3_2
    {Q z : ℕ} (hQ : 0 < Q)
    (major minor : Finset (ZMod Q))
    (I : Finset ℕ) (hIpos : ∀ n ∈ I, 0 < n)
    (hIdiv : ∀ n ∈ I, n ∣ Q)
    (p : ℕ → ℝ)
    (hp0 : ∀ n ∈ I, 0 ≤ p n) (hp1 : ∀ n ∈ I, p n ≤ 1)
    [NeZero Q]
    (hdisjoint : Disjoint major minor)
    (hcover : major ∪ minor =
      (Finset.univ.erase 0 : Finset (ZMod Q)))
    (hmajor : 3 / 4 ≤ 1 +
      (fourierBlock major I (fun n ↦ (Q / n : ZMod Q)) p z).re)
    (hminor :
      ‖fourierBlock minor I (fun n ↦ (Q / n : ZMod Q)) p z‖ ≤ 1 / 4)
    (htail :
      offLatticeMass I (fun n ↦ Q / n) p z Q ≤ 1 / (4 * (Q : ℝ))) :
    1 / (4 * (Q : ℝ)) ≤
      exactReciprocalMass I p (z / (Q : ℚ)) := by
  rw [← exactBernoulliMass_commonMultiple_eq_exactReciprocalMass
    hQ I hIpos hIdiv p]
  exact liuSawhney_local_limit_of_major_minor major minor I
    (fun n ↦ Q / n) p z hp0 hp1 hdisjoint hcover hmajor hminor htail

/-- Active-LCM specialization with the reciprocal tail discharged by the
finite Hoeffding estimate at the ambient smooth-LCM scale.  The latter is
stronger because the active LCM divides the smooth LCM. -/
theorem liuSawhney_proposition_3_2_activeLcm_of_major_minor
    {N M S z : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) (hS : 1 ≤ S)
    (I : Finset ℕ) (hI : I ⊆ goodDenominators N M S)
    [NeZero (activeLcm I)]
    (major minor : Finset (ZMod (activeLcm I)))
    (p : ℕ → ℝ)
    (hp0 : ∀ n ∈ I, 0 ≤ p n) (hp1 : ∀ n ∈ I, p n ≤ 1)
    (hmean : subsetMean I p (fun n : ℕ ↦ (n : ℝ)⁻¹) =
      (z : ℝ) / (activeLcm I : ℝ))
    (hdisjoint : Disjoint major minor)
    (hcover : major ∪ minor =
      (Finset.univ.erase 0 : Finset (ZMod (activeLcm I))))
    (hmajor : 3 / 4 ≤ 1 +
      (fourierBlock major I
        (fun n ↦ (activeLcm I / n : ZMod (activeLcm I))) p z).re)
    (hminor :
      ‖fourierBlock minor I
        (fun n ↦ (activeLcm I / n : ZMod (activeLcm I))) p z‖ ≤ 1 / 4)
    (hscale : (24 : ℝ) * (N : ℝ) * (S : ℝ) ≤ (M : ℝ) ^ 2)
    (hQ : (smoothLcm S : ℝ) ≤ Real.exp (5 * (S : ℝ))) :
    1 / (4 * (activeLcm I : ℝ)) ≤
      exactReciprocalMass I p (z / (activeLcm I : ℚ)) := by
  apply liuSawhney_proposition_3_2 (activeLcm_pos I) major minor I
  · intro n hn
    exact goodDenominator_pos hM (hI hn)
  · intro n hn
    exact dvd_activeLcm_of_mem_of_pos
      (fun k hk ↦ goodDenominator_pos hM (hI hk)) hn
  · exact hp0
  · exact hp1
  · exact hdisjoint
  · exact hcover
  · exact hmajor
  · exact hminor
  · refine (offLatticeMass_le_reciprocalEventMass_of_commonMultiple
      (activeLcm_pos I) I
      (fun n hn ↦ goodDenominator_pos hM (hI hn))
      (fun n hn ↦ dvd_activeLcm_of_mem_of_pos
        (fun k hk ↦ goodDenominator_pos hM (hI hk)) hn)
      p hp0 hp1).trans ?_
    have hIcc : I ⊆ Finset.Icc M N :=
      hI.trans (goodDenominators_subset_Icc N M S)
    have htail := abs_reciprocal_sum_sub_mean_tail_le_inv_four_smoothLcm
      p (Nat.lt_of_lt_of_le Nat.zero_lt_one hM) hMN hS hIcc hp0 hp1 hscale hQ
    have hfull : eventMass I p (fun B ↦
        1 ≤ |subsetSum B (fun n : ℕ ↦ (n : ℝ)⁻¹) -
          (z : ℝ) / (activeLcm I : ℝ)|) ≤
        1 / (4 * (smoothLcm S : ℝ)) := by
      simpa only [hmean] using htail
    refine hfull.trans ?_
    apply one_div_le_one_div_of_le
    · exact mul_pos (by norm_num) (by exact_mod_cast activeLcm_pos I)
    · exact mul_le_mul_of_nonneg_left
        (by exact_mod_cast activeLcm_le_smoothLcm hM hI) (by norm_num)

/-- Canonical-frequency version of the active-LCM assembly.  MajorArc's
`majorFrequencies` and `minorFrequencies` partition every nonzero character,
so only the two analytic arc estimates remain as inputs. -/
theorem liuSawhney_proposition_3_2_activeLcm_of_arc_bounds
    {N M S : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) (hS : 1 ≤ S)
    (I : Finset ℕ) (hI : I ⊆ goodDenominators N M S)
    [NeZero (activeLcm I)] (p : ℕ → ℝ)
    (hp0 : ∀ n ∈ I, 0 ≤ p n) (hp1 : ∀ n ∈ I, p n ≤ 1)
    (hmean : subsetMean I p (fun n : ℕ ↦ (n : ℝ)⁻¹) = 1)
    (hmajor : 3 / 4 ≤ 1 +
      (Erdos297.MajorArc.fourierBlock
        (Erdos297.MajorArc.majorFrequencies (activeLcm I) M) I
        (fun n ↦ (activeLcm I / n : ZMod (activeLcm I))) p
        (activeLcm I : ZMod (activeLcm I))).re)
    (hminor :
      ‖Erdos297.MajorArc.fourierBlock
        (Erdos297.MajorArc.minorFrequencies (activeLcm I) M) I
        (fun n ↦ (activeLcm I / n : ZMod (activeLcm I))) p
        (activeLcm I : ZMod (activeLcm I))‖ ≤ 1 / 4)
    (hscale : (24 : ℝ) * (N : ℝ) * (S : ℝ) ≤ (M : ℝ) ^ 2)
    (hQ : (smoothLcm S : ℝ) ≤ Real.exp (5 * (S : ℝ))) :
    1 / (4 * (activeLcm I : ℝ)) ≤ exactReciprocalMass I p 1 := by
  have hmean' : subsetMean I p (fun n : ℕ ↦ (n : ℝ)⁻¹) =
      ((activeLcm I : ℕ) : ℝ) / (activeLcm I : ℝ) := by
    simpa [activeLcm_ne_zero I] using hmean
  have hactive := liuSawhney_proposition_3_2_activeLcm_of_major_minor
    hM hMN hS I hI
    (Erdos297.MajorArc.majorFrequencies (activeLcm I) M)
    (Erdos297.MajorArc.minorFrequencies (activeLcm I) M)
    p hp0 hp1 hmean'
    (Erdos297.MajorArc.disjoint_major_minor (activeLcm I) M)
    (Erdos297.MajorArc.major_union_minor (activeLcm I) M)
    (by simpa [fourierBlock, Erdos297.MajorArc.fourierBlock] using hmajor)
    (by simpa [fourierBlock, Erdos297.MajorArc.fourierBlock] using hminor)
    hscale hQ
  simpa [activeLcm_ne_zero I] using hactive

/-- Canonical active-LCM assembly from the two arc estimates and the already
normalized reciprocal Hoeffding tail.  Its conclusion is deliberately
weakened from the active-LCM atom size to the ambient smooth-LCM atom size,
which is the form used by the entropy argument. -/
theorem liuSawhney_proposition_3_2_activeLcm_of_arc_bounds_and_tail
    {N M S : ℕ} (hM : 1 ≤ M)
    (I : Finset ℕ) (hI : I ⊆ goodDenominators N M S)
    [NeZero (activeLcm I)] (p : ℕ → ℝ)
    (hp0 : ∀ n ∈ I, 0 ≤ p n) (hp1 : ∀ n ∈ I, p n ≤ 1)
    (hmean : subsetMean I p (fun n : ℕ ↦ (n : ℝ)⁻¹) = 1)
    (hmajor : 3 / 4 ≤ 1 +
      (Erdos297.MajorArc.fourierBlock
        (Erdos297.MajorArc.majorFrequencies (activeLcm I) M) I
        (fun n ↦ (activeLcm I / n : ZMod (activeLcm I))) p
        (activeLcm I : ZMod (activeLcm I))).re)
    (hminor :
      ‖Erdos297.MajorArc.fourierBlock
        (Erdos297.MajorArc.minorFrequencies (activeLcm I) M) I
        (fun n ↦ (activeLcm I / n : ZMod (activeLcm I))) p
        (activeLcm I : ZMod (activeLcm I))‖ ≤ 1 / 4)
    (htail : eventMass I p (fun B ↦
      1 ≤ |subsetSum B (fun n : ℕ ↦ (n : ℝ)⁻¹) -
        subsetMean I p (fun n : ℕ ↦ (n : ℝ)⁻¹)|) ≤
      1 / (4 * (smoothLcm S : ℝ))) :
    1 / (4 * (smoothLcm S : ℝ)) ≤ exactReciprocalMass I p 1 := by
  have hIpos : ∀ n ∈ I, 0 < n := fun n hn ↦
    goodDenominator_pos hM (hI hn)
  have hIdiv : ∀ n ∈ I, n ∣ activeLcm I := fun n hn ↦
    dvd_activeLcm_of_mem_of_pos hIpos hn
  have htailActive :
      offLatticeMass I (fun n ↦ activeLcm I / n) p (activeLcm I)
          (activeLcm I) ≤ 1 / (4 * (activeLcm I : ℝ)) := by
    have hbridge := offLatticeMass_le_reciprocalEventMass_of_commonMultiple
      (activeLcm_pos I) I hIpos hIdiv p hp0 hp1
      (z := activeLcm I)
    have htoFull :
        offLatticeMass I (fun n ↦ activeLcm I / n) p (activeLcm I)
            (activeLcm I) ≤ 1 / (4 * (smoothLcm S : ℝ)) := by
      refine hbridge.trans ?_
      simpa [hmean, activeLcm_ne_zero I] using htail
    refine htoFull.trans ?_
    apply one_div_le_one_div_of_le
    · exact mul_pos (by norm_num) (by exact_mod_cast activeLcm_pos I)
    · exact mul_le_mul_of_nonneg_left
        (by exact_mod_cast activeLcm_le_smoothLcm hM hI) (by norm_num)
  have hactive := liuSawhney_proposition_3_2
    (activeLcm_pos I)
    (Erdos297.MajorArc.majorFrequencies (activeLcm I) M)
    (Erdos297.MajorArc.minorFrequencies (activeLcm I) M)
    I hIpos hIdiv p hp0 hp1
    (Erdos297.MajorArc.disjoint_major_minor (activeLcm I) M)
    (Erdos297.MajorArc.major_union_minor (activeLcm I) M)
    (by simpa [fourierBlock, Erdos297.MajorArc.fourierBlock] using hmajor)
    (by simpa [fourierBlock, Erdos297.MajorArc.fourierBlock] using hminor)
    htailActive
  have hactiveOne :
      1 / (4 * (activeLcm I : ℝ)) ≤ exactReciprocalMass I p 1 := by
    simpa [activeLcm_ne_zero I] using hactive
  exact (one_div_le_one_div_of_le
    (mul_pos (by norm_num) (by exact_mod_cast activeLcm_pos I))
    (mul_le_mul_of_nonneg_left
      (by exact_mod_cast activeLcm_le_smoothLcm hM hI) (by norm_num))).trans
    hactiveOne

/-- Eventual local-limit conclusion for the normalized source measure once
the concrete minor-arc estimate has been supplied.  The major arc,
normalization, probability range and off-lattice tail are all discharged
here from their source-scale theorems. -/
theorem eventually_local_limit_normalizedLogistic_of_minorArc
    {lam : ℝ} (hlam : IsUniqueCriticalParameter lam)
    (hminor : ∀ᶠ N : ℕ in atTop,
      ‖Erdos297.MinorArc.normalizedMinorBlock lam N‖ ≤ 1 / 4) :
    ∀ᶠ N : ℕ in atTop,
      1 / (4 * (smoothLcm (S N) : ℝ)) ≤
        exactReciprocalMass
          (Erdos297.LogisticNormalization.goodSet N)
          (Erdos297.LogisticNormalization.normalizedLogisticProbability lam N)
          1 := by
  filter_upwards [Erdos297.eventually_one_le_M,
    Erdos297.LogisticNormalization.eventually_normalized_probability_mem_Ioo hlam,
    Erdos297.LogisticNormalization.eventually_normalized_reciprocal_mean_eq_one hlam,
    eventually_abs_reciprocal_sum_sub_mean_tail_le_inv_four_smoothLcm,
    Erdos297.MajorEventual.eventually_normalized_majorArc_lower hlam,
    hminor] with N hM hp hmean htail hmajor hminorN
  let I := Erdos297.LogisticNormalization.goodSet N
  let p := Erdos297.LogisticNormalization.normalizedLogisticProbability lam N
  let : NeZero (activeLcm I) := ⟨activeLcm_ne_zero I⟩
  have hI : I ⊆ goodDenominators N (M N) (S N) := by
    simpa [I, Erdos297.LogisticNormalization.goodSet]
  have hIcc : I ⊆ Icc (M N) N := by
    simpa [I, Erdos297.LogisticNormalization.goodSet] using
      goodDenominators_subset_Icc N (M N) (S N)
  have hp0 : ∀ n ∈ I, 0 ≤ p n := by
    intro n hn
    exact (hp n (by simpa [I] using hn)).1.le
  have hp1 : ∀ n ∈ I, p n ≤ 1 := by
    intro n hn
    exact (hp n (by simpa [I] using hn)).2.le
  have hmean' :
      subsetMean I p (fun n : ℕ ↦ (n : ℝ)⁻¹) = 1 := by
    simpa [I, p, subsetMean, div_eq_mul_inv] using hmean
  have htail' := htail I p hIcc hp0 hp1
  have hmajor' : 3 / 4 ≤ 1 +
      (Erdos297.MajorArc.fourierBlock
        (Erdos297.MajorArc.majorFrequencies (activeLcm I) (M N)) I
        (fun n ↦ (activeLcm I / n : ZMod (activeLcm I))) p
        (activeLcm I : ZMod (activeLcm I))).re := by
    simpa [Erdos297.MajorArc.normalizedMajorBlock, I, p] using hmajor
  have hminor' :
      ‖Erdos297.MajorArc.fourierBlock
        (Erdos297.MajorArc.minorFrequencies (activeLcm I) (M N)) I
        (fun n ↦ (activeLcm I / n : ZMod (activeLcm I))) p
        (activeLcm I : ZMod (activeLcm I))‖ ≤ 1 / 4 := by
    simpa [Erdos297.MinorArc.normalizedMinorBlock,
      Erdos297.MajorArc.fourierBlock, I, p] using hminorN
  exact liuSawhney_proposition_3_2_activeLcm_of_arc_bounds_and_tail
    hM I hI p hp0 hp1 hmean' hmajor' hminor' htail'

/-- Liu--Sawhney Proposition 3.2 for the concrete normalized critical
logistic measure.  All major-arc, minor-arc, arithmetic and tail hypotheses
are discharged; the ambient smooth LCM is used only in the stated lower
bound, while Fourier inversion itself uses the source-correct active LCM. -/
theorem eventually_local_limit_normalizedLogistic
    {lam : ℝ} (hlam : IsUniqueCriticalParameter lam) :
    ∀ᶠ N : ℕ in atTop,
      1 / (4 * (smoothLcm (S N) : ℝ)) ≤
        exactReciprocalMass
          (Erdos297.LogisticNormalization.goodSet N)
          (Erdos297.LogisticNormalization.normalizedLogisticProbability lam N)
          1 :=
  eventually_local_limit_normalizedLogistic_of_minorArc hlam
    (Erdos297.MinorEventual.eventually_normalized_minorArc_bound hlam)

end

end Erdos297.LocalLimit

#print axioms Erdos297.LocalLimit.liuSawhney_proposition_3_2
#print axioms Erdos297.LocalLimit.eventually_local_limit_normalizedLogistic
