/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import ErdosProblems.Erdos730.BranchEvents
import ErdosProblems.Erdos730.PrimeBands
import ErdosProblems.Erdos730.PNTAP
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Erdős 730: transition-range event count

This file closes the range
`sqrt X < p ≤ sqrt X * (log X)^2` for the exact local branch-event ledger.
The finite argument forgets the unique exact cofactor, counts at most one
root class per prime and branch, and then invokes the reciprocal-prime band
limit and the ordinary prime-counting consequence of PNT in modulus one.
-/

open Filter Finset
open scoped Topology

namespace Erdos730.TransitionDensity

open BranchEvents DensityEvents FullDensityCore ConsecutiveTransition
open FullDensity

/-! ## Exact endpoints -/

/-- Natural upper cutoff `floor(sqrt X * (log X)^2)`. -/
noncomputable def transitionTopCut (X : ℕ) : ℕ :=
  ⌊transitionPrimeBandUpper (X : ℝ)⌋₊

/-- The primes in the exact transition interval. -/
noncomputable def transitionPrimeSet (X : ℕ) : Finset ℕ :=
  (Ioc (Nat.sqrt X) (transitionTopCut X)).filter Nat.Prime

/-! ## One root progression per branch and prime -/

def branchSlope : Branch → ℕ
  | .P => 222138
  | .Q => 380808
  | .R => 148092
  | .S => 380808

def branchOffset : Branch → ℕ
  | .P => 11
  | .Q => 13
  | .R => 5
  | .S => 19

theorem branchValue_eq_slope_mul_add (L : Branch) (x : ℕ) :
    branchValue L x = branchSlope L * x + branchOffset L := by
  cases L with
  | P => simpa [branchValue, branchSlope, branchOffset] using
      (branch_expansions x).1
  | Q => simpa [branchValue, branchSlope, branchOffset] using
      (branch_expansions x).2.1
  | R => simpa [branchValue, branchSlope, branchOffset] using
      (branch_expansions x).2.2.1
  | S => simpa [branchValue, branchSlope, branchOffset] using
      (branch_expansions x).2.2.2

theorem branchSlope_pos (L : Branch) : 0 < branchSlope L := by
  cases L <;> norm_num [branchSlope]

theorem branchSlope_le_max (L : Branch) : branchSlope L ≤ 380808 := by
  cases L <;> norm_num [branchSlope]

noncomputable def branchDivisibilityParameters
    (L : Branch) (p X : ℕ) : Finset ℕ :=
  (parameterRange X).filter fun x => p ∣ branchValue L x

theorem branchRoots_modEq
    {L : Branch} {p x y : ℕ} (hp : p.Prime)
    (hslope : branchSlope L < p)
    (hx : p ∣ branchValue L x) (hy : p ∣ branchValue L y) :
    x ≡ y [MOD p] := by
  have hvalues : branchValue L x ≡ branchValue L y [MOD p] :=
    hx.modEq_zero_nat.trans hy.modEq_zero_nat.symm
  rw [branchValue_eq_slope_mul_add, branchValue_eq_slope_mul_add] at hvalues
  have hmul : branchSlope L * x ≡ branchSlope L * y [MOD p] :=
    (Nat.ModEq.refl (branchOffset L)).add_right_cancel hvalues
  have hnot : ¬p ∣ branchSlope L :=
    Nat.not_dvd_of_pos_of_lt (branchSlope_pos L) hslope
  have hcop : Nat.Coprime p (branchSlope L) :=
    (hp.coprime_iff_not_dvd).2 hnot
  exact Nat.ModEq.cancel_left_of_coprime hcop.gcd_eq_one hmul

/-- A finite set contained in one residue class modulo `p` and in `[1,X]`
has at most `X/p+1` elements. -/
theorem card_le_div_add_one_of_modEq
    {S : Finset ℕ} {p v X : ℕ}
    (hbound : ∀ x ∈ S, x ≤ X)
    (hmod : ∀ x ∈ S, x ≡ v [MOD p]) :
    S.card ≤ X / p + 1 := by
  have hcard := Finset.card_le_card_of_injOn
    (fun x : ℕ => x / p)
    (s := S) (t := Finset.range (X / p + 1))
    (fun x hx => by
      simpa using Nat.lt_succ_of_le
        (Nat.div_le_div_right (hbound x hx)))
    (fun x hx y hy hdiv => by
      change x / p = y / p at hdiv
      have hxy : x ≡ y [MOD p] :=
        (hmod x hx).trans (hmod y hy).symm
      unfold Nat.ModEq at hxy
      calc
        x = p * (x / p) + x % p := (Nat.div_add_mod x p).symm
        _ = p * (y / p) + y % p := by rw [hdiv, hxy]
        _ = y := Nat.div_add_mod y p)
  simpa using hcard

theorem branchDivisibilityParameters_card_le
    {L : Branch} {p X : ℕ} (hp : p.Prime)
    (hslope : branchSlope L < p) :
    (branchDivisibilityParameters L p X).card ≤ X / p + 1 := by
  classical
  by_cases hempty : branchDivisibilityParameters L p X = ∅
  · simp [hempty]
  · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    apply card_le_div_add_one_of_modEq
    · intro x hx
      exact (mem_parameterRange.mp
        (Finset.mem_filter.mp hx).1).2
    · intro x hx
      exact branchRoots_modEq hp hslope
        (Finset.mem_filter.mp hx).2
        (Finset.mem_filter.mp hv).2

/-! ## Injecting transition witnesses into branch-prime-root triples -/

abbrev TransitionKey := Σ _L : Branch, Σ _p : ℕ, ℕ

def transitionWitnessKey (w : LocalBranchWitness) : TransitionKey :=
  ⟨localWitnessBranch w,
    ⟨localWitnessPrime w, localWitnessParameter w⟩⟩

noncomputable def transitionDivisibilityKeys (X : ℕ) : Finset TransitionKey :=
  (Finset.univ : Finset Branch).sigma fun L =>
    (transitionPrimeSet X).sigma fun p =>
      branchDivisibilityParameters L p X

theorem transitionWitnessKey_mapsTo (X : ℕ) :
    Set.MapsTo transitionWitnessKey
      (localTransitionPrimeWitnessesUpTo X (Nat.sqrt X) (transitionTopCut X) :
        Set LocalBranchWitness)
      (transitionDivisibilityKeys X : Set TransitionKey) := by
  intro w hw
  change w ∈ localTransitionPrimeWitnessesUpTo X (Nat.sqrt X)
    (transitionTopCut X) at hw
  change transitionWitnessKey w ∈ transitionDivisibilityKeys X
  have htrans := Finset.mem_filter.mp hw
  have hlocal := mem_localBranchWitnessesUpTo.mp htrans.1
  rw [transitionDivisibilityKeys]
  simp only [transitionWitnessKey, Finset.mem_sigma, Finset.mem_univ,
    true_and]
  constructor
  · rw [transitionPrimeSet, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨htrans.2.2.1, htrans.2.2.2⟩, hlocal.2.1⟩
  · rw [branchDivisibilityParameters, Finset.mem_filter]
    exact ⟨(mem_witnessBox.mp hlocal.1).1,
      prime_dvd_factor_of_exactPrimePowerCofactor hlocal.2.2.2.1⟩

theorem transitionWitnessKey_injOn (X : ℕ) :
    Set.InjOn transitionWitnessKey
      (localTransitionPrimeWitnessesUpTo X (Nat.sqrt X) (transitionTopCut X) :
        Set LocalBranchWitness) := by
  rintro ⟨L, x, p, a, d⟩ hw ⟨K, y, q, b, e⟩ hv hkey
  simp only [transitionWitnessKey, localWitnessBranch, localWitnessPrime,
    localWitnessParameter, Sigma.mk.injEq] at hkey
  rcases hkey with ⟨rfl, rfl, rfl⟩
  have hwa := (Finset.mem_filter.mp hw).2.1
  have hvb := (Finset.mem_filter.mp hv).2.1
  change a = 1 at hwa
  change b = 1 at hvb
  subst a
  subst b
  have hwd := (mem_localBranchWitnessesUpTo.mp
    (Finset.mem_filter.mp hw).1).2.2.2.1.2.1
  have hve := (mem_localBranchWitnessesUpTo.mp
    (Finset.mem_filter.mp hv).1).2.2.2.1.2.1
  change branchValue L x = p ^ 1 * d at hwd
  change branchValue L x = p ^ 1 * e at hve
  have hp : 0 < p := (mem_localBranchWitnessesUpTo.mp
    (Finset.mem_filter.mp hw).1).2.1.pos
  have hde : d = e := by
    apply Nat.mul_left_cancel (pow_pos hp 1)
    rw [← hwd, ← hve]
  subst e
  rfl

theorem transitionWitnesses_card_le_keys (X : ℕ) :
    (localTransitionPrimeWitnessesUpTo X (Nat.sqrt X)
      (transitionTopCut X)).card ≤
        (transitionDivisibilityKeys X).card :=
  Finset.card_le_card_of_injOn transitionWitnessKey
    (transitionWitnessKey_mapsTo X) (transitionWitnessKey_injOn X)

theorem transitionDivisibilityKeys_card (X : ℕ) :
    (transitionDivisibilityKeys X).card =
      ∑ L : Branch, ∑ p ∈ transitionPrimeSet X,
        (branchDivisibilityParameters L p X).card := by
  simp [transitionDivisibilityKeys, Finset.card_sigma]

/-- Exact finite transition count before casting to the analytic bound. -/
theorem transitionWitnesses_card_le_sum (X : ℕ)
    (hroot : 380808 ≤ Nat.sqrt X) :
    (localTransitionPrimeWitnessesUpTo X (Nat.sqrt X)
      (transitionTopCut X)).card ≤
        4 * ∑ p ∈ transitionPrimeSet X, (X / p + 1) := by
  calc
    _ ≤ (transitionDivisibilityKeys X).card :=
      transitionWitnesses_card_le_keys X
    _ = ∑ L : Branch, ∑ p ∈ transitionPrimeSet X,
        (branchDivisibilityParameters L p X).card :=
      transitionDivisibilityKeys_card X
    _ ≤ ∑ _L : Branch, ∑ p ∈ transitionPrimeSet X,
        (X / p + 1) := by
      apply Finset.sum_le_sum
      intro L _hL
      apply Finset.sum_le_sum
      intro p hp
      have hpMem := Finset.mem_filter.mp hp
      exact branchDivisibilityParameters_card_le hpMem.2
        ((branchSlope_le_max L).trans_lt
          (hroot.trans_lt (Finset.mem_Ioc.mp hpMem.1).1))
    _ = _ := by
      have hcard : Fintype.card Branch = 4 := by decide
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcard]
      norm_num

/-! ## Reciprocal-prime mass of the exact natural interval -/

noncomputable def transitionPrimeMass (X : ℕ) : ℝ :=
  ∑ p ∈ transitionPrimeSet X, (p : ℝ)⁻¹

theorem transitionPrimeMass_eq_band {X : ℕ}
    (hcut : Nat.sqrt X ≤ transitionTopCut X) :
    transitionPrimeMass X = transitionReciprocalPrimeBand (X : ℝ) := by
  have hdis : Disjoint
      ((Ioc 0 (Nat.sqrt X)).filter Nat.Prime)
      ((Ioc (Nat.sqrt X) (transitionTopCut X)).filter Nat.Prime) :=
    Finset.disjoint_filter_filter
      (Finset.Ioc_disjoint_Ioc_of_le (le_refl (Nat.sqrt X)))
  have hunion :
      (Ioc 0 (Nat.sqrt X)).filter Nat.Prime ∪
          (Ioc (Nat.sqrt X) (transitionTopCut X)).filter Nat.Prime =
        (Ioc 0 (transitionTopCut X)).filter Nat.Prime := by
    rw [← Finset.filter_union,
      Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hcut]
  have hsum := Finset.sum_union hdis
    (f := fun p : ℕ ↦ (p : ℝ)⁻¹)
  rw [hunion] at hsum
  unfold transitionPrimeMass transitionPrimeSet
  rw [transitionReciprocalPrimeBand, reciprocalPrimeSumReal,
    reciprocalPrimeSumReal, transitionPrimeBandLower, transitionTopCut,
    Real.nat_floor_real_sqrt_eq_nat_sqrt]
  unfold transitionTopCut at hsum
  linarith

theorem eventually_sqrt_le_transitionTopCut :
    ∀ᶠ X : ℕ in atTop, Nat.sqrt X ≤ transitionTopCut X := by
  filter_upwards [eventually_ge_atTop 3] with X hX
  rw [← Real.nat_floor_real_sqrt_eq_nat_sqrt]
  apply Nat.floor_mono
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hexp : Real.exp 1 < (X : ℝ) :=
    Real.exp_one_lt_three.trans_le (by exact_mod_cast hX)
  have hlog : 1 < Real.log (X : ℝ) := by
    apply Real.exp_lt_exp.mp
    simpa [Real.exp_log hXpos] using hexp
  have hsqrt : 0 ≤ Real.sqrt (X : ℝ) := Real.sqrt_nonneg _
  unfold transitionPrimeBandUpper
  nlinarith [sq_nonneg (Real.log (X : ℝ) - 1)]

theorem tendsto_transitionPrimeMass :
    Tendsto transitionPrimeMass atTop (𝓝 0) := by
  apply tendsto_transitionReciprocalPrimeBand_nat.congr'
  filter_upwards [eventually_sqrt_le_transitionTopCut] with X hcut
  exact (transitionPrimeMass_eq_band hcut).symm

/-! ## Real form of the finite event bound -/

theorem transitionWitnesses_cast_card_le (X : ℕ)
    (hroot : 380808 ≤ Nat.sqrt X) :
    ((localTransitionPrimeWitnessesUpTo X (Nat.sqrt X)
      (transitionTopCut X)).card : ℝ) ≤
        4 * ((X : ℝ) * transitionPrimeMass X +
          (transitionPrimeSet X).card) := by
  have hnat := transitionWitnesses_card_le_sum X hroot
  calc
    ((localTransitionPrimeWitnessesUpTo X (Nat.sqrt X)
      (transitionTopCut X)).card : ℝ) ≤
        ((4 * ∑ p ∈ transitionPrimeSet X, (X / p + 1) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    _ = 4 * ∑ p ∈ transitionPrimeSet X,
        (((X / p + 1 : ℕ) : ℝ)) := by push_cast; ring
    _ ≤ 4 * ∑ p ∈ transitionPrimeSet X,
        ((X : ℝ) / (p : ℝ) + 1) := by
      gcongr with p hp
      simpa only [Nat.cast_add, Nat.cast_one] using
        add_le_add (Nat.cast_div_le (m := X) (n := p) (α := ℝ)) le_rfl
    _ = 4 * ((X : ℝ) * transitionPrimeMass X +
        (transitionPrimeSet X).card) := by
      unfold transitionPrimeMass
      simp_rw [div_eq_mul_inv]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp

theorem normalized_transitionWitnesses_le (X : ℕ)
    (hX : 0 < X) (hroot : 380808 ≤ Nat.sqrt X) :
    ((localTransitionPrimeWitnessesUpTo X (Nat.sqrt X)
        (transitionTopCut X)).card : ℝ) / (X : ℝ) ≤
      4 * transitionPrimeMass X +
        4 * (transitionPrimeSet X).card / (X : ℝ) := by
  calc
    _ ≤ (4 * ((X : ℝ) * transitionPrimeMass X +
        (transitionPrimeSet X).card)) / (X : ℝ) :=
      div_le_div_of_nonneg_right (transitionWitnesses_cast_card_le X hroot)
        (Nat.cast_nonneg X)
    _ = _ := by
      have hX0 : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
      field_simp

/-! ## The prime-counting endpoint term -/

theorem tendsto_transitionPrimeBandUpper_atTop :
    Tendsto transitionPrimeBandUpper atTop atTop := by
  have hlogSq : Tendsto (fun X : ℝ ↦ Real.log X ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      Real.tendsto_log_atTop
  exact Real.tendsto_sqrt_atTop.atTop_mul_atTop₀ hlogSq

theorem tendsto_transitionPrimeBandUpper_nat_atTop :
    Tendsto (fun X : ℕ ↦ transitionPrimeBandUpper (X : ℝ))
      atTop atTop :=
  tendsto_transitionPrimeBandUpper_atTop.comp tendsto_natCast_atTop_atTop

theorem tendsto_transitionPrimeBandUpper_div :
    Tendsto (fun X : ℝ ↦ transitionPrimeBandUpper X / X)
      atTop (𝓝 0) := by
  have hbase : Tendsto
      (fun X : ℝ ↦ Real.log (Real.sqrt X) ^ 2 / Real.sqrt X)
      atTop (𝓝 0) := by
    simpa using!
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
        Real.tendsto_sqrt_atTop
  have hscaled : Tendsto
      (fun X : ℝ ↦
        4 * (Real.log (Real.sqrt X) ^ 2 / Real.sqrt X))
      atTop (𝓝 0) := by
    simpa using hbase.const_mul 4
  apply hscaled.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  have hsqrt0 : Real.sqrt X ≠ 0 := (Real.sqrt_pos.2 hX).ne'
  unfold transitionPrimeBandUpper
  rw [Real.log_sqrt hX.le]
  field_simp
  nlinarith [Real.sq_sqrt hX.le]

theorem tendsto_transitionPrimeBandUpper_div_nat :
    Tendsto (fun X : ℕ ↦
      transitionPrimeBandUpper (X : ℝ) / (X : ℝ))
      atTop (𝓝 0) :=
  tendsto_transitionPrimeBandUpper_div.comp tendsto_natCast_atTop_atTop

private theorem tendsto_transitionPrimeCounting_normalized :
    Tendsto (fun X : ℕ ↦
      primeAPCountingReal 1 0 (transitionPrimeBandUpper (X : ℝ)) /
        (transitionPrimeBandUpper (X : ℝ) /
          Real.log (transitionPrimeBandUpper (X : ℝ))))
      atTop (𝓝 1) := by
  have h := (primeAPCountingReal_normalized_tendsto
    (A := 1) (a := 0) (by norm_num) (by norm_num) (by norm_num)).comp
      tendsto_transitionPrimeBandUpper_nat_atTop
  simpa using! h

private theorem tendsto_transitionPNTScale :
    Tendsto (fun X : ℕ ↦
      (transitionPrimeBandUpper (X : ℝ) /
        Real.log (transitionPrimeBandUpper (X : ℝ))) / (X : ℝ))
      atTop (𝓝 0) := by
  have hinvLog : Tendsto (fun X : ℕ ↦
      (Real.log (transitionPrimeBandUpper (X : ℝ)))⁻¹)
      atTop (𝓝 0) :=
    (Real.tendsto_log_atTop.comp
      tendsto_transitionPrimeBandUpper_nat_atTop).inv_tendsto_atTop
  have hmul := tendsto_transitionPrimeBandUpper_div_nat.mul hinvLog
  have hmul' : Tendsto (fun X : ℕ ↦
      (transitionPrimeBandUpper (X : ℝ) / (X : ℝ)) *
        (Real.log (transitionPrimeBandUpper (X : ℝ)))⁻¹)
      atTop (𝓝 0) := by simpa using hmul
  apply hmul'.congr'
  exact Eventually.of_forall fun X ↦ by ring

theorem tendsto_transitionPrimeCounting_div :
    Tendsto (fun X : ℕ ↦
      primeAPCountingReal 1 0 (transitionPrimeBandUpper (X : ℝ)) /
        (X : ℝ)) atTop (𝓝 0) := by
  have hprod := tendsto_transitionPrimeCounting_normalized.mul
    tendsto_transitionPNTScale
  have hprod' : Tendsto (fun X : ℕ ↦
      (primeAPCountingReal 1 0 (transitionPrimeBandUpper (X : ℝ)) /
        (transitionPrimeBandUpper (X : ℝ) /
          Real.log (transitionPrimeBandUpper (X : ℝ)))) *
      ((transitionPrimeBandUpper (X : ℝ) /
        Real.log (transitionPrimeBandUpper (X : ℝ))) / (X : ℝ)))
      atTop (𝓝 0) := by simpa using hprod
  apply hprod'.congr'
  filter_upwards
      [tendsto_transitionPrimeBandUpper_nat_atTop.eventually_gt_atTop
        (Real.exp 1), eventually_gt_atTop (0 : ℕ)] with X hupper hX
  have hu0 : transitionPrimeBandUpper (X : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.exp_pos 1 |>.trans hupper)
  have hlog0 : Real.log (transitionPrimeBandUpper (X : ℝ)) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact Real.exp_pos 1 |>.trans hupper
    · linarith [Real.exp_one_gt_two]
  have hX0 : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
  field_simp

theorem transitionPrimeSet_card_le_primeCounting (X : ℕ) :
    ((transitionPrimeSet X).card : ℝ) ≤
      primeAPCountingReal 1 0 (transitionPrimeBandUpper (X : ℝ)) := by
  unfold primeAPCountingReal
  norm_cast
  apply Finset.card_le_card
  intro p hp
  rw [transitionPrimeSet, Finset.mem_filter, Finset.mem_Ioc] at hp
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨Nat.zero_le p, ?_⟩, hp.2, Nat.mod_one p⟩
  simpa [transitionTopCut] using hp.1.2

theorem tendsto_transitionPrimeSet_card_div :
    Tendsto (fun X : ℕ ↦
      ((transitionPrimeSet X).card : ℝ) / (X : ℝ))
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun X ↦ by positivity
  · exact Eventually.of_forall fun X ↦
      div_le_div_of_nonneg_right
        (transitionPrimeSet_card_le_primeCounting X) (Nat.cast_nonneg X)
  · exact tendsto_transitionPrimeCounting_div

/-! ## Transition density closure -/

/-- The normalized exact transition-range local witness count. -/
noncomputable def normalizedTransitionWitnessCount (X : ℕ) : ℝ :=
  ((localTransitionPrimeWitnessesUpTo X (Nat.sqrt X)
    (transitionTopCut X)).card : ℝ) / (X : ℝ)

/-- The transition-range contribution is `o(X)`. -/
theorem tendsto_normalizedTransitionWitnessCount :
    Tendsto normalizedTransitionWitnessCount atTop (𝓝 0) := by
  have hmajorant : Tendsto (fun X : ℕ ↦
      4 * transitionPrimeMass X +
        4 * (transitionPrimeSet X).card / (X : ℝ))
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add, mul_div_assoc] using
      (tendsto_transitionPrimeMass.const_mul 4).add
        (tendsto_transitionPrimeSet_card_div.const_mul 4)
  apply squeeze_zero'
  · exact Eventually.of_forall fun X ↦ by
      unfold normalizedTransitionWitnessCount
      positivity
  · filter_upwards
      [eventually_ge_atTop (380808 * 380808)] with X hX
    unfold normalizedTransitionWitnessCount
    apply normalized_transitionWitnesses_le X
    · omega
    · exact Nat.le_sqrt.mpr hX
  · exact hmajorant

end Erdos730.TransitionDensity
