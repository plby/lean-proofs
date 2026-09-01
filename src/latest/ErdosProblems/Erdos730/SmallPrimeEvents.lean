/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import ErdosProblems.Erdos730.FixedDepthFourier
import ErdosProblems.Erdos730.FiniteBlockCount
import ErdosProblems.Erdos730.FixedDepthDensity
import ErdosProblems.Erdos730.HigherPowerEvents
import ErdosProblems.Erdos730.LimsupSeries
import ErdosProblems.Erdos730.LowerHalfFourier
import ErdosProblems.Erdos730.PNTAP
import ErdosProblems.Erdos730.SmallPrimeDepth
import ErdosProblems.Erdos730.SmallPrimeTail

/-!
# Erdős 730: concrete small-prime events

This file connects the exact local-obstruction ledger to the fixed-depth and
uniform-tail estimates in the first-power range `p ≤ sqrt X`.

The finite part is unconditional.  A witnessed tuple is injected into the
key `(branch, prime, parameter)`, and each fixed key is counted by the
root-progression fiber already constructed in `Erdos730HigherPowerEvents`.
At exponent one the generic padded-block estimate gives the uniform bound

`#fiber / X ≤ (3 / p) * ((p+1)/(2p))^r`.

The sharp fixed-depth estimate is kept behind one explicitly local Fourier
interface near the end of the file.  No density statement, target theorem,
or uniformity in the depth is assumed there.
-/

open Filter Finset
open scoped Topology

namespace Erdos730.SmallPrimeEvents

open BranchEvents DensityEvents DigitBoxes FullDensity FullDensityCore
open FiniteBlockCount FixedDepthDensity FixedDepthFourier
open HigherPowerEvents KummerTransition LimsupSeries RangeAssembly
open LowerHalfFourier
open SmallPrimeDepth SmallPrimeTail

noncomputable section

/-! ## A real-valued wrapper around finite complete-block counting -/

/-- A real upper bound for each complete block may be rounded up once.  If
the discrepancy is at least one, that rounding is absorbed by doubling the
discrepancy.  The actual prefix decomposition is the exact natural theorem
in `Erdos730FiniteBlockCount`. -/
theorem card_filter_range_cast_le_completeBlocks_add_terminal
    (N P : ℕ) (accept : ℕ → Prop) [DecidablePred accept]
    (hP : 0 < P) (main D : ℝ) (hmain : 0 ≤ main) (hD : 1 ≤ D)
    (hblock : ∀ k : ℕ,
      (((Finset.range P).filter fun t ↦ accept (t + P * k)).card : ℝ) ≤
        main + D) :
    (((Finset.range N).filter accept).card : ℝ) ≤
      ((N / P : ℕ) : ℝ) * (main + 2 * D) + P := by
  let B : ℕ := ⌈main + D⌉₊
  have hsum0 : 0 ≤ main + D := by linarith
  have hblockNat (k : ℕ) :
      ((Finset.range P).filter fun t ↦ accept (t + P * k)).card ≤ B := by
    have hreal := (hblock k).trans (Nat.le_ceil (main + D))
    exact_mod_cast hreal
  have hnat := card_filter_range_le_completeBlocks_add_terminal
    N P B accept hP hblockNat
  have hB : (B : ℝ) ≤ main + 2 * D := by
    have hceil := (Nat.ceil_lt_add_one hsum0).le
    dsimp only [B]
    linarith
  calc
    (((Finset.range N).filter accept).card : ℝ) ≤
        (((N / P) * B + P : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = ((N / P : ℕ) : ℝ) * (B : ℝ) + (P : ℝ) := by
      push_cast
      ring
    _ ≤ ((N / P : ℕ) : ℝ) * (main + 2 * D) + P := by
      gcongr

/-- Natural representative of the common quadratic coefficient. -/
def fixedDepthNaturalAlpha : ℕ := 84591927504

theorem fixedDepthNaturalAlpha_intCast :
    (fixedDepthNaturalAlpha : ℤ) = commonQuadraticCoefficient := by
  norm_num [fixedDepthNaturalAlpha, commonQuadraticCoefficient,
    ObstructionMaps.Tz_eq]

/-- All prime divisors of the quadratic coefficient are at most `43`. -/
theorem largePrime_not_dvd_fixedDepthNaturalAlpha
    {p : ℕ} (hp : p.Prime) (hp43 : 43 < p) :
    ¬p ∣ fixedDepthNaturalAlpha := by
  intro h
  have hfac : fixedDepthNaturalAlpha =
      2 ^ 4 * 3 ^ 5 * 7 * 41 ^ 2 * 43 ^ 2 := by
    norm_num [fixedDepthNaturalAlpha]
  rw [hfac] at h
  rcases hp.dvd_mul.mp h with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · have hp2 := hp.dvd_of_dvd_pow h
          have := Nat.le_of_dvd (by norm_num : 0 < 2) hp2
          omega
        · have hp3 := hp.dvd_of_dvd_pow h
          have := Nat.le_of_dvd (by norm_num : 0 < 3) hp3
          omega
      · have := Nat.le_of_dvd (by norm_num : 0 < 7) h
        omega
    · have hp41 := hp.dvd_of_dvd_pow h
      have := Nat.le_of_dvd (by norm_num : 0 < 41) hp41
      omega
  · have hp43' := hp.dvd_of_dvd_pow h
    have := Nat.le_of_dvd (by norm_num : 0 < 43) hp43'
    omega

/-- The standard representative of a unit modulo `p^j` is not divisible by
`p` when `j > 0`. -/
theorem zmod_val_not_dvd_prime_of_isUnit
    {p j : ℕ} [NeZero (p ^ j)] (hp : p.Prime) (hj : 1 ≤ j)
    (z : ZMod (p ^ j)) (hz : IsUnit z) : ¬p ∣ z.val := by
  have hzcast : IsUnit (z.val : ZMod (p ^ j)) := by
    rw [ZMod.natCast_zmod_val]
    exact hz
  have hcop := (ZMod.isUnit_iff_coprime z.val (p ^ j)).mp hzcast
  intro hpval
  have hppow : p ∣ p ^ j := dvd_pow_self p (by omega)
  have hcop' : p.Coprime p :=
    Nat.Coprime.of_dvd_right hppow
      (Nat.Coprime.of_dvd_left hpval hcop)
  exact hp.ne_one ((Nat.coprime_self p).mp hcop')

/-- Natural representative of the linear coefficient in the branch phase. -/
def fixedDepthNaturalBeta (p r : ℕ) (L : Branch) (c₀ : ℕ) : ℕ :=
  ((p : ZMod (p ^ (2 * r))) *
      (branchPadicLinear L p 1 c₀ : ZMod (p ^ (2 * r))) +
    (branchResidualCoefficient L : ZMod (p ^ (2 * r)))).val

/-- Natural representative of the constant coefficient in the branch phase. -/
def fixedDepthNaturalGamma
    (p r : ℕ) (L : Branch) (s c₀ : ℕ) : ℕ :=
  ((branchTestValue L s c₀ : ℕ) : ZMod (p ^ (2 * r))).val

theorem fixedDepthNaturalAlpha_cast
    {p r : ℕ} [NeZero p] :
    (fixedDepthNaturalAlpha : ZMod (p ^ (2 * r))) =
      (branchPadicQuadratic p 1 : ZMod (p ^ (2 * r))) := by
  rw [show (fixedDepthNaturalAlpha : ZMod (p ^ (2 * r))) =
      ((fixedDepthNaturalAlpha : ℤ) : ZMod (p ^ (2 * r))) by
    norm_num]
  rw [fixedDepthNaturalAlpha_intCast]
  simp [branchPadicQuadratic]

theorem fixedDepthNaturalBeta_cast
    {p r : ℕ} [NeZero p] (L : Branch) (c₀ : ℕ) :
    (fixedDepthNaturalBeta p r L c₀ : ZMod (p ^ (2 * r))) =
      (p : ZMod (p ^ (2 * r))) *
          (branchPadicLinear L p 1 c₀ : ZMod (p ^ (2 * r))) +
        (branchResidualCoefficient L : ZMod (p ^ (2 * r))) := by
  exact ZMod.natCast_zmod_val _

theorem fixedDepthNaturalGamma_cast
    {p r : ℕ} [NeZero p] (L : Branch) (s c₀ : ℕ) :
    (fixedDepthNaturalGamma p r L s c₀ : ZMod (p ^ (2 * r))) =
      (branchTestValue L s c₀ : ZMod (p ^ (2 * r))) := by
  exact ZMod.natCast_zmod_val _

/-- The linear coefficient is a unit modulo `p^(2r)`, because its residual
part is a unit and the remaining summand is nilpotent. -/
theorem prime_not_dvd_fixedDepthNaturalBeta
    {L : Branch} {x p a d r c₀ : ℕ}
    (hr : 1 ≤ r) (hlocal : LocalBranchObstruction L x p a d) :
    ¬p ∣ fixedDepthNaturalBeta p r L c₀ := by
  let : NeZero p := ⟨hlocal.1.ne_zero⟩
  let Q : ℕ := p ^ (2 * r)
  have hunitResidual :
      IsUnit (branchResidualCoefficient L : ZMod Q) := by
    simpa only [Q] using
      (branchResidualCoefficient_isUnit (r := 2 * r) hlocal)
  have hnil : IsNilpotent
      ((p : ZMod Q) * (branchPadicLinear L p 1 c₀ : ZMod Q)) :=
    zmod_primeMultiple_isNilpotent _
  have hunitSum : IsUnit
      ((p : ZMod Q) * (branchPadicLinear L p 1 c₀ : ZMod Q) +
        (branchResidualCoefficient L : ZMod Q)) :=
    hnil.isUnit_add_right_of_commute hunitResidual (Commute.all _ _)
  have hunitBeta :
      IsUnit (fixedDepthNaturalBeta p r L c₀ : ZMod Q) := by
    rw [show
      (fixedDepthNaturalBeta p r L c₀ : ZMod Q) =
        (p : ZMod Q) * (branchPadicLinear L p 1 c₀ : ZMod Q) +
          (branchResidualCoefficient L : ZMod Q) by
      simpa only [Q] using fixedDepthNaturalBeta_cast L c₀]
    exact hunitSum
  have hcop : Nat.Coprime (fixedDepthNaturalBeta p r L c₀) Q :=
    (ZMod.isUnit_iff_coprime _ _).1 hunitBeta
  intro hdiv
  have hpQ : p ∣ Q := by
    dsimp only [Q]
    exact dvd_pow_self p (by omega)
  have hpgcd : p ∣ Nat.gcd (fixedDepthNaturalBeta p r L c₀) Q :=
    Nat.dvd_gcd hdiv hpQ
  rw [hcop.gcd_eq_one] at hpgcd
  exact hlocal.1.ne_one (Nat.dvd_one.mp hpgcd)

/-- Exact conversion of the root-progression phase to the natural
coefficient presentation consumed by the fixed-depth Fourier theorem. -/
theorem padicBranchMap_eq_fixedDepthQuadratic
    {p r : ℕ} [NeZero p] (L : Branch) (s c₀ : ℕ)
    (k : ZMod (p ^ (2 * r))) :
    padicBranchMap (p : ZMod (p ^ (2 * r)))
        (branchPadicQuadratic p 1 : ZMod (p ^ (2 * r)))
        (branchPadicLinear L p 1 c₀ : ZMod (p ^ (2 * r)))
        (branchResidualCoefficient L : ZMod (p ^ (2 * r)))
        (branchTestValue L s c₀ : ZMod (p ^ (2 * r))) k =
      fixedDepthQuadratic
        (fixedDepthNaturalAlpha : ZMod (p ^ (2 * r)))
        (fixedDepthNaturalBeta p r L c₀ : ZMod (p ^ (2 * r)))
        (fixedDepthNaturalGamma p r L s c₀ : ZMod (p ^ (2 * r))) k := by
  rw [fixedDepthNaturalAlpha_cast, fixedDepthNaturalBeta_cast,
    fixedDepthNaturalGamma_cast]
  simp only [padicBranchMap, fixedDepthQuadratic]

/-! ## Exact prime bands and keyed fibers -/

/-- Primes in the exact natural-number depth band at height `X`. -/
def smallPrimeBandPrimes (X r : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (Nat.sqrt X)).filter fun p ↦
    p.Prime ∧ smallPrimeDepth p X = r

/-- Primes in the residual depth tail at height `X`. -/
def smallPrimeTailPrimes (X R : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (Nat.sqrt X)).filter fun p ↦
    p.Prime ∧ R ≤ smallPrimeDepth p X

@[simp] theorem mem_smallPrimeBandPrimes {X r p : ℕ} :
    p ∈ smallPrimeBandPrimes X r ↔
      2 ≤ p ∧ p ≤ Nat.sqrt X ∧ p.Prime ∧
        smallPrimeDepth p X = r := by
  simp [smallPrimeBandPrimes, and_assoc]

@[simp] theorem mem_smallPrimeTailPrimes {X R p : ℕ} :
    p ∈ smallPrimeTailPrimes X R ↔
      2 ≤ p ∧ p ≤ Nat.sqrt X ∧ p.Prime ∧
        R ≤ smallPrimeDepth p X := by
  simp [smallPrimeTailPrimes, and_assoc]

/-- A small-prime witness is determined by its branch, prime, and parameter;
the exact cofactor is recovered from the factorization. -/
abbrev SmallPrimeKey := Σ _L : Branch, Σ _p : ℕ, ℕ

def smallPrimeWitnessKey (w : LocalBranchWitness) : SmallPrimeKey :=
  ⟨localWitnessBranch w,
    ⟨localWitnessPrime w, localWitnessParameter w⟩⟩

/-- Keys over an arbitrary finite set of first-power primes. -/
def smallPrimeKeys (X : ℕ) (s : Finset ℕ) : Finset SmallPrimeKey :=
  (Finset.univ : Finset Branch).sigma fun L ↦
    s.sigma fun p ↦ localHigherPowerFiber X L p 1

theorem smallPrimeKeys_card (X : ℕ) (s : Finset ℕ) :
    (smallPrimeKeys X s).card =
      ∑ L : Branch, ∑ p ∈ s, (localHigherPowerFiber X L p 1).card := by
  simp [smallPrimeKeys, Finset.card_sigma]

theorem smallPrimeDepthWitnessKey_mapsTo (X r : ℕ) :
    Set.MapsTo smallPrimeWitnessKey
      (localSmallPrimeDepthWitnessesUpTo X r : Set LocalBranchWitness)
      (smallPrimeKeys X (smallPrimeBandPrimes X r) : Set SmallPrimeKey) := by
  intro w hw
  rcases mem_localSmallPrimeDepthWitnessesUpTo.mp hw with ⟨hsmall, hdepth⟩
  rcases Finset.mem_filter.mp hsmall with ⟨hledger, ha, hpSmall⟩
  have hlocal := mem_localBranchWitnessesUpTo.mp hledger
  have hx : localWitnessParameter w ∈ parameterRange X :=
    (mem_witnessBox.mp hlocal.1).1
  change smallPrimeWitnessKey w ∈
    smallPrimeKeys X (smallPrimeBandPrimes X r)
  rw [smallPrimeKeys]
  simp only [smallPrimeWitnessKey, Finset.mem_sigma, Finset.mem_univ,
    true_and]
  constructor
  · exact mem_smallPrimeBandPrimes.mpr
      ⟨hlocal.2.1.two_le, hpSmall, hlocal.2.1, hdepth⟩
  · exact mem_localHigherPowerFiber.mpr
      ⟨hx, ⟨localWitnessCofactor w, by simpa [ha] using hlocal.2⟩⟩

theorem smallPrimeTailWitnessKey_mapsTo (X R : ℕ) :
    Set.MapsTo smallPrimeWitnessKey
      (localSmallPrimeDepthTailWitnessesUpTo X R : Set LocalBranchWitness)
      (smallPrimeKeys X (smallPrimeTailPrimes X R) : Set SmallPrimeKey) := by
  intro w hw
  rcases mem_localSmallPrimeDepthTailWitnessesUpTo.mp hw with
    ⟨hsmall, hdepth⟩
  rcases Finset.mem_filter.mp hsmall with ⟨hledger, ha, hpSmall⟩
  have hlocal := mem_localBranchWitnessesUpTo.mp hledger
  have hx : localWitnessParameter w ∈ parameterRange X :=
    (mem_witnessBox.mp hlocal.1).1
  change smallPrimeWitnessKey w ∈
    smallPrimeKeys X (smallPrimeTailPrimes X R)
  rw [smallPrimeKeys]
  simp only [smallPrimeWitnessKey, Finset.mem_sigma, Finset.mem_univ,
    true_and]
  constructor
  · exact mem_smallPrimeTailPrimes.mpr
      ⟨hlocal.2.1.two_le, hpSmall, hlocal.2.1, hdepth⟩
  · exact mem_localHigherPowerFiber.mpr
      ⟨hx, ⟨localWitnessCofactor w, by simpa [ha] using hlocal.2⟩⟩

/-- The `(branch, prime, parameter)` key is injective on the exponent-one
ledger.  This is where uniqueness of the exact cofactor is used. -/
theorem smallPrimeWitnessKey_injOn (X : ℕ) :
    Set.InjOn smallPrimeWitnessKey
      (localSmallPrimeWitnessesUpTo X (Nat.sqrt X) :
        Set LocalBranchWitness) := by
  rintro ⟨L, x, p, a, d⟩ hw ⟨K, y, q, b, e⟩ hv hkey
  have hL : L = K := congrArg (fun z : SmallPrimeKey ↦ z.1) hkey
  have hpq : p = q := congrArg (fun z : SmallPrimeKey ↦ z.2.1) hkey
  have hxy : x = y := congrArg (fun z : SmallPrimeKey ↦ z.2.2) hkey
  subst K
  subst q
  subst y
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
    apply Nat.mul_left_cancel hp
    simpa using hwd.symm.trans hve
  subst e
  rfl

theorem localSmallPrimeDepthWitnesses_card_le_keys (X r : ℕ) :
    (localSmallPrimeDepthWitnessesUpTo X r).card ≤
      (smallPrimeKeys X (smallPrimeBandPrimes X r)).card := by
  apply Finset.card_le_card_of_injOn smallPrimeWitnessKey
      (smallPrimeDepthWitnessKey_mapsTo X r)
  exact smallPrimeWitnessKey_injOn X |>.mono fun _ hw ↦
    (mem_localSmallPrimeDepthWitnessesUpTo.mp hw).1

theorem localSmallPrimeDepthTailWitnesses_card_le_keys (X R : ℕ) :
    (localSmallPrimeDepthTailWitnessesUpTo X R).card ≤
      (smallPrimeKeys X (smallPrimeTailPrimes X R)).card := by
  apply Finset.card_le_card_of_injOn smallPrimeWitnessKey
      (smallPrimeTailWitnessKey_mapsTo X R)
  exact smallPrimeWitnessKey_injOn X |>.mono fun _ hw ↦
    (mem_localSmallPrimeDepthTailWitnessesUpTo.mp hw).1

/-- Depth zero is absent from the exact small-prime ledger. -/
theorem localSmallPrimeDepthWitnesses_zero_eq_empty (X : ℕ) :
    localSmallPrimeDepthWitnessesUpTo X 0 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro w hw
  rcases mem_localSmallPrimeDepthWitnessesUpTo.mp hw with
    ⟨hsmall, hdepth⟩
  rcases Finset.mem_filter.mp hsmall with ⟨hlocal, _ha, hpSmall⟩
  have hlocal' := mem_localBranchWitnessesUpTo.mp hlocal
  have hX : 0 < X := by
    have hx := mem_parameterRange.mp (mem_witnessBox.mp hlocal'.1).1
    omega
  have hdepthPos :=
    (smallPrimeDepth_spec hlocal'.2.1 hX hpSmall).1
  omega

@[simp] theorem normalizedSmallPrimeDepthWitnessCount_zero (X : ℕ) :
    normalizedSmallPrimeDepthWitnessCount 0 X = 0 := by
  simp [normalizedSmallPrimeDepthWitnessCount,
    localSmallPrimeDepthWitnesses_zero_eq_empty]

/-! ## Uniform complete-block estimate for one fiber -/

theorem higherPowerDepth_one_eq_smallPrimeDepth (p X : ℕ) :
    higherPowerDepth p 1 X = smallPrimeDepth p X := by
  simp [higherPowerDepth, smallPrimeDepth, Nat.log_div_base]

theorem higherPowerRho_le_two_thirds
    {p : ℕ} (hp3 : 3 ≤ p) : higherPowerRho p ≤ (2 / 3 : ℝ) := by
  unfold higherPowerRho
  have hp0 : (0 : ℝ) < p := by positivity
  have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * p)]
  norm_num
  linarith

/-- Equation (43), with every floor and padded block retained. -/
theorem localSmallPrimeFiber_normalized_le_uniform
    {X p r : ℕ} {L : Branch}
    (hX : 0 < X) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpSmall : p ≤ Nat.sqrt X)
    (hr : smallPrimeDepth p X = r) :
    ((localHigherPowerFiber X L p 1).card : ℝ) / (X : ℝ) ≤
      (3 / (p : ℝ)) * (2 / 3 : ℝ) ^ r := by
  have hp3 : 3 ≤ p :=
    Nat.succ_le_iff.mpr (lt_of_le_of_ne hp.two_le (Ne.symm hp2))
  let U : ℕ := X / p
  let P : ℕ := p ^ r
  let H : ℕ := halfDigitCount p
  let B : ℕ := (localHigherPowerFiber X L p 1).card
  have hspec := smallPrimeDepth_spec hp hX hpSmall
  have hr1 : 1 ≤ r := by simpa [hr] using hspec.1
  have hPX : p * P ≤ X := by
    simpa [P, hr, pow_succ', Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using hspec.2.1
  have hPPos : 0 < P := pow_pos hp.pos r
  have hPleU : P ≤ U := by
    rw [Nat.le_div_iff_mul_le hp.pos]
    simpa [P, mul_comm] using hPX
  have hDPos : 0 < U / P := Nat.div_pos hPleU hPPos
  have hcoeff : (U + 1) / P + 1 ≤ 3 * (U / P) := by
    have hs := HigherPowerEvents.succ_div_le_div_add_one U P
    omega
  have hblock : B ≤ ((U + 1) / P + 1) * H ^ r := by
    have h := localHigherPowerFiber_card_le_block
      (X := X) (p := p) (a := 1) (L := L)
    simpa [B, U, P, H, higherPowerDepth_one_eq_smallPrimeDepth, hr]
      using h
  have hUP : (U / P) * P ≤ U := Nat.div_mul_le_self U P
  have hpU : p * U ≤ X := by
    simpa [U, mul_comm] using Nat.div_mul_le_self X p
  have hnat : B * p * P ≤ 3 * X * H ^ r := by
    calc
      B * p * P ≤
          (((U + 1) / P + 1) * H ^ r) * p * P :=
        Nat.mul_le_mul_right P (Nat.mul_le_mul_right p hblock)
      _ ≤ (3 * (U / P) * H ^ r) * p * P := by
        exact Nat.mul_le_mul_right P (Nat.mul_le_mul_right p
          (Nat.mul_le_mul_right (H ^ r) hcoeff))
      _ = 3 * H ^ r * p * ((U / P) * P) := by ring
      _ ≤ 3 * H ^ r * p * U :=
        Nat.mul_le_mul_left _ hUP
      _ ≤ 3 * H ^ r * X :=
        by simpa [mul_assoc] using Nat.mul_le_mul_left (3 * H ^ r) hpU
      _ = 3 * X * H ^ r := by ring
  have hreal : (B : ℝ) * (p : ℝ) * (P : ℝ) ≤
      3 * (X : ℝ) * (H : ℝ) ^ r := by
    exact_mod_cast hnat
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hPR : (0 : ℝ) < P := by exact_mod_cast hPPos
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hratio : (B : ℝ) / (X : ℝ) ≤
      (3 / (p : ℝ)) * ((H : ℝ) / (p : ℝ)) ^ r := by
    have hquot : (B : ℝ) / (X : ℝ) ≤
        (3 * (H : ℝ) ^ r) / ((p : ℝ) * (P : ℝ)) := by
      apply (div_le_div_iff₀ hXR (mul_pos hpR hPR)).2
      simpa [mul_assoc, mul_left_comm, mul_comm] using hreal
    calc
      (B : ℝ) / (X : ℝ) ≤
          (3 * (H : ℝ) ^ r) / ((p : ℝ) * (P : ℝ)) := hquot
      _ = (3 / (p : ℝ)) * ((H : ℝ) / (p : ℝ)) ^ r := by
        simp only [P, Nat.cast_pow, div_pow]
        field_simp
  have hrho : ((H : ℝ) / (p : ℝ)) ≤ (2 / 3 : ℝ) := by
    rw [show (H : ℝ) / (p : ℝ) = higherPowerRho p by
      simpa [H] using halfDigitCount_cast_div_eq_rho hp hp2]
    exact higherPowerRho_le_two_thirds hp3
  calc
    ((localHigherPowerFiber X L p 1).card : ℝ) / (X : ℝ) =
        (B : ℝ) / (X : ℝ) := by rfl
    _ ≤ (3 / (p : ℝ)) * ((H : ℝ) / (p : ℝ)) ^ r := hratio
    _ ≤ (3 / (p : ℝ)) * (2 / 3 : ℝ) ^ r := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hrho r) (by positivity)

/-! ## Sharp fixed-depth count for one branch and prime -/

/-- The concrete finite Fourier estimate for one branch/prime fiber.  The
complete-block multiplier is the natural floor
`(X / p + 1) / p^r`; retaining it is essential for the normalized Fourier
error bound. -/
theorem localSmallPrimeFiber_card_cast_le_fixedDepthRaw
    {X p r : ℕ} {L : Branch}
    (hX : 0 < X) (hp : p.Prime) (hp43 : 43 < p)
    (hpSmall : p ≤ Nat.sqrt X)
    (hdepth : smallPrimeDepth p X = r) :
    ((localHigherPowerFiber X L p 1).card : ℝ) ≤
      ((((X / p + 1) / p ^ r : ℕ) : ℝ) *
          (((lowerHalfResidues p (2 * r)).card : ℝ) *
              (p ^ r : ℕ) / (p ^ (2 * r) : ℕ) +
            2 * fixedDepthBlockDiscrepancy r p)) +
        (p ^ r : ℕ) := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hp3 : 3 ≤ p := by omega
  have hr : 1 ≤ r := by
    simpa only [hdepth] using (smallPrimeDepth_spec hp hX hpSmall).1
  let : NeZero p := ⟨hp.ne_zero⟩
  by_cases hempty : localHigherPowerFiber X L p 1 = ∅
  · rw [hempty]
    simp only [card_empty, Nat.cast_zero]
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (add_nonneg (by positivity)
          (mul_nonneg (by norm_num)
            (fixedDepthBlockDiscrepancy_nonneg r p))))
      (Nat.cast_nonneg _)
  · obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    rcases mem_localHigherPowerFiber.mp hx₀ with ⟨_hx₀Range, d₀, h₀⟩
    let s : ℕ := x₀ % p
    let c₀ : ℕ := branchValue L s / p
    let A : Finset (ZMod (p ^ (2 * r))) := lowerHalfResidues p (2 * r)
    let F : ℕ → ZMod (p ^ (2 * r)) := fun k ↦
      fixedDepthQuadratic
        (fixedDepthNaturalAlpha : ZMod (p ^ (2 * r)))
        (fixedDepthNaturalBeta p r L c₀ : ZMod (p ^ (2 * r)))
        (fixedDepthNaturalGamma p r L s c₀ : ZMod (p ^ (2 * r)))
        (k : ZMod (p ^ (2 * r)))
    let admissible : Finset ℕ :=
      (Finset.range (X / p + 1)).filter fun k ↦ F k ∈ A
    have hmap : ∀ x ∈ localHigherPowerFiber X L p 1,
        x / p ∈ admissible := by
      intro x hx
      rcases mem_localHigherPowerFiber.mp hx with ⟨hxRange, d, hlocal⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_, ?_⟩
      · exact Nat.lt_succ_of_le (Nat.div_le_div_right
          (mem_parameterRange.mp hxRange).2)
      · have hdigit := natCast_mem_lowerHalfResidues (r := 2 * r)
          hlocal.1 hlocal.2.1 hlocal.2.2.2
        change F (x / p) ∈ A
        have hphase : F (x / p) =
            (branchTestValue L x d : ZMod (p ^ (2 * r))) := by
          rw [show F (x / p) =
              padicBranchMap (p : ZMod (p ^ (2 * r)))
                (branchPadicQuadratic p 1 : ZMod (p ^ (2 * r)))
                (branchPadicLinear L p 1 c₀ : ZMod (p ^ (2 * r)))
                (branchResidualCoefficient L : ZMod (p ^ (2 * r)))
                (branchTestValue L s c₀ : ZMod (p ^ (2 * r)))
                (x / p : ZMod (p ^ (2 * r))) by
            dsimp only [F]
            exact (padicBranchMap_eq_fixedDepthQuadratic L s c₀ _).symm]
          simpa only [s, c₀, pow_one] using
            (branchTestValue_eq_padicBranchMap
              (r := 2 * r) h₀ hlocal).symm
        rw [hphase]
        simpa only [A] using hdigit
    have hinj : Set.InjOn (fun x : ℕ ↦ x / p)
        (localHigherPowerFiber X L p 1 : Set ℕ) := by
      intro x hx y hy hdiv
      rcases mem_localHigherPowerFiber.mp hx with ⟨_hxRange, d, hxlocal⟩
      rcases mem_localHigherPowerFiber.mp hy with ⟨_hyRange, e, hylocal⟩
      change x / p = y / p at hdiv
      have hmod : x % p = y % p := by
        have hxy : x ≡ y [MOD p] := by
          simpa only [pow_one] using localBranchRoots_modEq hxlocal hylocal
        exact hxy
      calc
        x = p * (x / p) + x % p := (Nat.div_add_mod x p).symm
        _ = p * (y / p) + y % p := by rw [hdiv, hmod]
        _ = y := Nat.div_add_mod y p
    have hfiber : (localHigherPowerFiber X L p 1).card ≤ admissible.card :=
      Finset.card_le_card_of_injOn (fun x : ℕ ↦ x / p) hmap hinj
    have hA :
        (∑ h : ZMod (p ^ (2 * r)),
            ‖ZMod.dft (finsetIndicator A) h‖) ≤
          ((p ^ (2 * r) : ℕ) : ℝ) *
            (3 + Real.log p) ^ (2 * r) := by
      simpa only [A, Nat.cast_pow] using
        (dft_lowerHalfResidues_l1_le (p := p) (d := 2 * r) hp3)
    have hblock (k : ℕ) :
        (((Finset.range (p ^ r)).filter fun t ↦
            F (t + p ^ r * k) ∈ A).card : ℝ) ≤
          ((A.card : ℝ) * (p ^ r : ℕ) / (p ^ (2 * r) : ℕ)) +
            fixedDepthBlockDiscrepancy r p := by
      have hfourier := fixedDepth_intervalHitCount_le
        (p := p) (r := r)
        (alpha := fixedDepthNaturalAlpha)
        (beta := fixedDepthNaturalBeta p r L c₀)
        (gamma := fixedDepthNaturalGamma p r L s c₀)
        hp hr hp2
        (largePrime_not_dvd_fixedDepthNaturalAlpha hp hp43)
        (prime_not_dvd_fixedDepthNaturalBeta (c₀ := c₀) hr h₀)
        (p ^ r * k) A hA
      simpa only [intervalHitCount, F, fixedDepthBlockDiscrepancy,
        add_comm] using hfourier
    have hadmissible : (admissible.card : ℝ) ≤
        ((((X / p + 1) / p ^ r : ℕ) : ℝ) *
          (((A.card : ℝ) * (p ^ r : ℕ) / (p ^ (2 * r) : ℕ)) +
            2 * fixedDepthBlockDiscrepancy r p)) +
          (p ^ r : ℕ) := by
      exact card_filter_range_cast_le_completeBlocks_add_terminal
        (X / p + 1) (p ^ r) (fun k ↦ F k ∈ A)
        (pow_pos hp.pos r)
        ((A.card : ℝ) * (p ^ r : ℕ) / (p ^ (2 * r) : ℕ))
        (fixedDepthBlockDiscrepancy r p)
        (by positivity)
        (one_le_fixedDepthBlockDiscrepancy hp.pos hr)
        hblock
    calc
      ((localHigherPowerFiber X L p 1).card : ℝ) ≤
          (admissible.card : ℝ) := by exact_mod_cast hfiber
      _ ≤ _ := by simpa only [A] using hadmissible

/-- Normalized one-fiber estimate in exactly the four summands used by the
fixed-depth analytic majorant. -/
theorem localSmallPrimeFiber_normalized_le_fixedDepth
    {X p r : ℕ} {L : Branch}
    (hX : 0 < X) (hp : p.Prime) (hp43 : 43 < p)
    (hpSmall : p ≤ Nat.sqrt X)
    (hdepth : smallPrimeDepth p X = r) :
    ((localHigherPowerFiber X L p 1).card : ℝ) / (X : ℝ) ≤
      relaxedDigitDensity r p / (p : ℝ) + 1 / (X : ℝ) +
        fixedDepthFourierErrorConstant r * fixedDepthFourierWeight r p +
          (p : ℝ) ^ r / (X : ℝ) := by
  have hp0 : 0 < p := hp.pos
  have hp3 : 3 ≤ p := by omega
  have hr : 1 ≤ r := by
    simpa only [hdepth] using (smallPrimeDepth_spec hp hX hpSmall).1
  let B : ℕ := (X / p + 1) / p ^ r
  let A : Finset (ZMod (p ^ (2 * r))) := lowerHalfResidues p (2 * r)
  have hraw := localSmallPrimeFiber_card_cast_le_fixedDepthRaw
    (L := L) hX hp hp43 hpSmall hdepth
  have hmain :
      ((A.card : ℝ) * (p ^ r : ℕ) / (p ^ (2 * r) : ℕ)) =
        relaxedDigitDensity r p * (p : ℝ) ^ r := by
    rw [relaxedDigitDensity_eq_card_ratio hp3]
    simp only [A, Nat.cast_pow]
    ring
  have hBPnat : B * p ^ r ≤ X / p + 1 := by
    exact Nat.div_mul_le_self (X / p + 1) (p ^ r)
  have hBP : (B : ℝ) * (p : ℝ) ^ r ≤ ((X / p + 1 : ℕ) : ℝ) := by
    exact_mod_cast hBPnat
  have hN : ((X / p + 1 : ℕ) : ℝ) ≤
      (X : ℝ) / (p : ℝ) + 1 := by
    push_cast
    linarith [(Nat.cast_div_le : ((X / p : ℕ) : ℝ) ≤
      (X : ℝ) / (p : ℝ))]
  have hdelta0 : 0 ≤ relaxedDigitDensity r p :=
    relaxedDigitDensity_nonneg r p
  have hmainBound :
      ((B : ℝ) *
          ((A.card : ℝ) * (p ^ r : ℕ) /
            (p ^ (2 * r) : ℕ))) / (X : ℝ) ≤
        relaxedDigitDensity r p / (p : ℝ) +
          relaxedDigitDensity r p / (X : ℝ) := by
    rw [hmain]
    have hprod :
        (B : ℝ) * (p : ℝ) ^ r * relaxedDigitDensity r p ≤
          ((X : ℝ) / (p : ℝ) + 1) * relaxedDigitDensity r p := by
      exact mul_le_mul_of_nonneg_right (hBP.trans hN) hdelta0
    have hXR : (0 : ℝ) < X := by exact_mod_cast hX
    calc
      (B : ℝ) * (relaxedDigitDensity r p * (p : ℝ) ^ r) /
          (X : ℝ) =
          ((B : ℝ) * (p : ℝ) ^ r * relaxedDigitDensity r p) /
            (X : ℝ) := by ring
      _ ≤ (((X : ℝ) / (p : ℝ) + 1) *
          relaxedDigitDensity r p) / (X : ℝ) :=
        div_le_div_of_nonneg_right hprod hXR.le
      _ = relaxedDigitDensity r p / (p : ℝ) +
          relaxedDigitDensity r p / (X : ℝ) := by
        have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
        have hXR0 : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
        field_simp [hpR, hXR0]
  have hband := (smallPrimeDepth_spec hp hX hpSmall).2.1
  rw [hdepth] at hband
  have hdisc :=
    two_mul_fixedDepthCompleteBlocks_normalized_discrepancy_le
      hp0 hX hr hband
  have hdeltaOne :
      relaxedDigitDensity r p / (X : ℝ) ≤ 1 / (X : ℝ) := by
    exact div_le_div_of_nonneg_right
      (relaxedDigitDensity_le_one hp.one_le) (by positivity)
  have hrawDiv :
      ((localHigherPowerFiber X L p 1).card : ℝ) / (X : ℝ) ≤
        (((B : ℝ) *
          (((A.card : ℝ) * (p ^ r : ℕ) /
              (p ^ (2 * r) : ℕ)) +
            2 * fixedDepthBlockDiscrepancy r p)) +
          (p : ℝ) ^ r) / (X : ℝ) := by
    have := div_le_div_of_nonneg_right hraw (by positivity : (0 : ℝ) ≤ X)
    simpa only [B, A, Nat.cast_pow] using this
  calc
    ((localHigherPowerFiber X L p 1).card : ℝ) / (X : ℝ) ≤
        (((B : ℝ) *
          (((A.card : ℝ) * (p ^ r : ℕ) /
              (p ^ (2 * r) : ℕ)) +
            2 * fixedDepthBlockDiscrepancy r p)) +
          (p : ℝ) ^ r) / (X : ℝ) := hrawDiv
    _ = ((B : ℝ) *
          ((A.card : ℝ) * (p ^ r : ℕ) /
            (p ^ (2 * r) : ℕ))) / (X : ℝ) +
        2 * (((B : ℝ) * fixedDepthBlockDiscrepancy r p) /
          (X : ℝ)) +
        (p : ℝ) ^ r / (X : ℝ) := by ring
    _ ≤ (relaxedDigitDensity r p / (p : ℝ) +
          relaxedDigitDensity r p / (X : ℝ)) +
        fixedDepthFourierErrorConstant r * fixedDepthFourierWeight r p +
        (p : ℝ) ^ r / (X : ℝ) := by
      exact add_le_add (add_le_add hmainBound hdisc) le_rfl
    _ ≤ relaxedDigitDensity r p / (p : ℝ) + 1 / (X : ℝ) +
        fixedDepthFourierErrorConstant r * fixedDepthFourierWeight r p +
        (p : ℝ) ^ r / (X : ℝ) := by
      gcongr

/-! ## Natural depth bands versus the real Mertens bands -/

/-- The floor-valued prime set occurring literally in
`fixedDepthReciprocalPrimeBand`. -/
def realDepthPrimeBand (X r : ℕ) : Finset ℕ :=
  (Finset.Ioc
      ⌊FullDensity.fixedDepthPrimeBandLower r (X : ℝ)⌋₊
      ⌊FullDensity.fixedDepthPrimeBandUpper r (X : ℝ)⌋₊).filter
    Nat.Prime

theorem smallPrimeBandPrimes_subset_realDepthPrimeBand
    {X r : ℕ} (hX : 0 < X) :
    smallPrimeBandPrimes X r ⊆ realDepthPrimeBand X r := by
  intro p hpBand
  rcases mem_smallPrimeBandPrimes.mp hpBand with
    ⟨_hp2, hpSmall, hp, hdepth⟩
  have hspec := smallPrimeDepth_spec hp hX hpSmall
  rw [hdepth] at hspec
  have hlowCast : (p : ℝ) ^ ((r + 1 : ℕ) : ℝ) ≤ (X : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hspec.2.1
  have hhighCast : (X : ℝ) <
      (p : ℝ) ^ ((r + 2 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hspec.2.2
  have hX0 : (0 : ℝ) ≤ X := by positivity
  have hp0 : (0 : ℝ) ≤ p := by positivity
  have hlower : fixedDepthPrimeBandLower r (X : ℝ) < (p : ℝ) := by
    exact (Real.rpow_inv_lt_iff_of_pos hX0 hp0 (by positivity)).2 hhighCast
  have hupper : (p : ℝ) ≤ fixedDepthPrimeBandUpper r (X : ℝ) := by
    exact (Real.le_rpow_inv_iff_of_pos hp0 hX0 (by positivity)).2 hlowCast
  rw [realDepthPrimeBand, Finset.mem_filter, Finset.mem_Ioc]
  refine ⟨⟨?_, Nat.le_floor hupper⟩, hp⟩
  exact (Nat.floor_lt (fixedDepthPrimeBandLower_pos r
    (by exact_mod_cast hX)).le).2 hlower

/-- At every positive fixed depth, the exact ledger count is eventually
dominated by four copies of the complete analytic majorant, one for each
branch. -/
theorem eventually_normalizedSmallPrimeDepthWitnessCount_le_majorant
    (r : ℕ) (hr : 1 ≤ r) :
    ∀ᶠ X : ℕ in atTop,
      normalizedSmallPrimeDepthWitnessCount r X ≤
        4 * fixedDepthAnalyticMajorant r X := by
  filter_upwards
      [(tendsto_fixedDepthPrimeBandLowerFloor r).eventually_ge_atTop 43,
        eventually_gt_atTop (0 : ℕ)] with X hfloor hX
  have hsubset : smallPrimeBandPrimes X r ⊆ fixedDepthPrimeSet r X := by
    simpa only [realDepthPrimeBand, fixedDepthPrimeSet] using
      (smallPrimeBandPrimes_subset_realDepthPrimeBand (X := X) (r := r) hX)
  let g : ℕ → ℝ := fun p ↦
    relaxedDigitDensity r p / (p : ℝ) + 1 / (X : ℝ) +
      fixedDepthFourierErrorConstant r * fixedDepthFourierWeight r p +
        (p : ℝ) ^ r / (X : ℝ)
  have hg_nonneg (p : ℕ) : 0 ≤ g p := by
    dsimp only [g]
    have hdelta := relaxedDigitDensity_nonneg r p
    have hweight : 0 ≤ fixedDepthFourierWeight r p := by
      unfold fixedDepthFourierWeight
      positivity
    have hconstant : 0 ≤ fixedDepthFourierErrorConstant r := by
      unfold fixedDepthFourierErrorConstant
      positivity
    positivity
  have hsumIdentity :
      (∑ p ∈ fixedDepthPrimeSet r X, g p) =
        fixedDepthAnalyticMajorant r X := by
    unfold g fixedDepthAnalyticMajorant fixedDepthFourierError
      fixedDepthFourierBandError fixedDepthTerminalBlockError
      fixedDepthUnitError
    simp_rw [Finset.sum_add_distrib, Finset.sum_div]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.mul_sum]
    ring
  have hprime (L : Branch) :
      (∑ p ∈ smallPrimeBandPrimes X r,
          ((localHigherPowerFiber X L p 1).card : ℝ) / (X : ℝ)) ≤
        fixedDepthAnalyticMajorant r X := by
    calc
      (∑ p ∈ smallPrimeBandPrimes X r,
          ((localHigherPowerFiber X L p 1).card : ℝ) / (X : ℝ)) ≤
          ∑ p ∈ smallPrimeBandPrimes X r, g p := by
        apply Finset.sum_le_sum
        intro p hpBand
        have hpBand' := mem_smallPrimeBandPrimes.mp hpBand
        have hpFull := hsubset hpBand
        have hp43 : 43 < p := by
          rw [fixedDepthPrimeSet, Finset.mem_filter, Finset.mem_Ioc] at hpFull
          omega
        exact localSmallPrimeFiber_normalized_le_fixedDepth
          (L := L) hX hpBand'.2.2.1 hp43 hpBand'.2.1 hpBand'.2.2.2
      _ ≤ ∑ p ∈ fixedDepthPrimeSet r X, g p := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun p _hpFull _hpBand ↦ hg_nonneg p)
      _ = fixedDepthAnalyticMajorant r X := hsumIdentity
  have hcard := localSmallPrimeDepthWitnesses_card_le_keys X r
  have hcast :
      ((localSmallPrimeDepthWitnessesUpTo X r).card : ℝ) ≤
        ((smallPrimeKeys X (smallPrimeBandPrimes X r)).card : ℝ) := by
    exact_mod_cast hcard
  unfold normalizedSmallPrimeDepthWitnessCount
  calc
    ((localSmallPrimeDepthWitnessesUpTo X r).card : ℝ) / (X : ℝ) ≤
        ((smallPrimeKeys X (smallPrimeBandPrimes X r)).card : ℝ) /
          (X : ℝ) := by
      exact div_le_div_of_nonneg_right hcast (by positivity)
    _ = ∑ L : Branch, ∑ p ∈ smallPrimeBandPrimes X r,
          ((localHigherPowerFiber X L p 1).card : ℝ) / (X : ℝ) := by
      rw [smallPrimeKeys_card]
      push_cast
      simp only [Finset.sum_div]
    _ ≤ ∑ _L : Branch, fixedDepthAnalyticMajorant r X := by
      exact Finset.sum_le_sum fun L _hL ↦ hprime L
    _ = 4 * fixedDepthAnalyticMajorant r X := by
      have hbranch : Fintype.card Branch = 4 := by decide
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hbranch]
      norm_num

theorem fixedDepthReciprocalPrimeBand_eq_sum_realDepthPrimeBand
    {X r : ℕ} (hX : 1 < X) :
    fixedDepthReciprocalPrimeBand r (X : ℝ) =
      ∑ p ∈ realDepthPrimeBand X r, (p : ℝ)⁻¹ := by
  let lo : ℕ := ⌊fixedDepthPrimeBandLower r (X : ℝ)⌋₊
  let hi : ℕ := ⌊fixedDepthPrimeBandUpper r (X : ℝ)⌋₊
  have hlohi : lo ≤ hi := by
    apply Nat.floor_mono
    exact fixedDepthPrimeBandLower_le_upper r (by exact_mod_cast hX.le)
  have hdisj : Disjoint
      ((Finset.Ioc 0 lo).filter Nat.Prime)
      ((Finset.Ioc lo hi).filter Nat.Prime) := by
    exact Finset.disjoint_filter_filter
      (Finset.Ioc_disjoint_Ioc_of_le (a := 0) (d := hi) le_rfl)
  have hunion :
      (Finset.Ioc 0 lo).filter Nat.Prime ∪
          (Finset.Ioc lo hi).filter Nat.Prime =
        (Finset.Ioc 0 hi).filter Nat.Prime := by
    rw [← Finset.filter_union,
      Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le lo) hlohi]
  have hsum := Finset.sum_union hdisj
      (f := fun p : ℕ ↦ (p : ℝ)⁻¹)
  rw [hunion] at hsum
  unfold fixedDepthReciprocalPrimeBand reciprocalPrimeSumReal
  change (∑ p ∈ (Finset.Ioc 0 hi).filter Nat.Prime, (p : ℝ)⁻¹) -
      (∑ p ∈ (Finset.Ioc 0 lo).filter Nat.Prime, (p : ℝ)⁻¹) = _
  rw [realDepthPrimeBand]
  change _ = ∑ p ∈ (Finset.Ioc lo hi).filter Nat.Prime, (p : ℝ)⁻¹
  linarith

/-- Reciprocal-prime mass of the exact natural depth band. -/
def smallPrimeBandMass (X r : ℕ) : ℝ :=
  ∑ p ∈ smallPrimeBandPrimes X r, (p : ℝ)⁻¹

/-- Geometrically weighted reciprocal-prime mass in the residual tail. -/
def weightedSmallPrimeTailMass (X R : ℕ) : ℝ :=
  ∑ p ∈ smallPrimeTailPrimes X R,
    (2 / 3 : ℝ) ^ smallPrimeDepth p X * (p : ℝ)⁻¹

theorem smallPrimeBandMass_nonneg (X r : ℕ) :
    0 ≤ smallPrimeBandMass X r := by
  unfold smallPrimeBandMass
  positivity

theorem weightedSmallPrimeTailMass_nonneg (X R : ℕ) :
    0 ≤ weightedSmallPrimeTailMass X R := by
  unfold weightedSmallPrimeTailMass
  positivity

theorem smallPrimeBandMass_le_fixedDepthReciprocalPrimeBand
    {X r : ℕ} (hX : 1 < X) :
    smallPrimeBandMass X r ≤
      fixedDepthReciprocalPrimeBand r (X : ℝ) := by
  rw [fixedDepthReciprocalPrimeBand_eq_sum_realDepthPrimeBand hX]
  unfold smallPrimeBandMass
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (smallPrimeBandPrimes_subset_realDepthPrimeBand (by omega))
    (fun p _ _ ↦ by positivity)

/-! ## Uniform tail: shallow and deepest bands -/

def shallowSmallPrimeTailPrimes (X R J : ℕ) : Finset ℕ :=
  (smallPrimeTailPrimes X R).filter fun p ↦ smallPrimeDepth p X < J

def deepSmallPrimeTailPrimes (X R J : ℕ) : Finset ℕ :=
  (smallPrimeTailPrimes X R).filter fun p ↦ J ≤ smallPrimeDepth p X

@[simp] theorem mem_shallowSmallPrimeTailPrimes {X R J p : ℕ} :
    p ∈ shallowSmallPrimeTailPrimes X R J ↔
      p ∈ smallPrimeTailPrimes X R ∧ smallPrimeDepth p X < J := by
  simp [shallowSmallPrimeTailPrimes]

@[simp] theorem mem_deepSmallPrimeTailPrimes {X R J p : ℕ} :
    p ∈ deepSmallPrimeTailPrimes X R J ↔
      p ∈ smallPrimeTailPrimes X R ∧ J ≤ smallPrimeDepth p X := by
  simp [deepSmallPrimeTailPrimes]

theorem shallowSmallPrimeTailPrimes_eq_biUnion (X R J : ℕ) :
    shallowSmallPrimeTailPrimes X R J =
      (Finset.Ico R J).biUnion (smallPrimeBandPrimes X) := by
  ext p
  constructor
  · intro hp
    rcases mem_shallowSmallPrimeTailPrimes.mp hp with ⟨htail, hJ⟩
    have htail' := mem_smallPrimeTailPrimes.mp htail
    rw [Finset.mem_biUnion]
    exact ⟨smallPrimeDepth p X,
      Finset.mem_Ico.mpr ⟨htail'.2.2.2, hJ⟩,
      mem_smallPrimeBandPrimes.mpr
        ⟨htail'.1, htail'.2.1, htail'.2.2.1, rfl⟩⟩
  · intro hp
    rcases Finset.mem_biUnion.mp hp with ⟨r, hr, hpBand⟩
    have hr' := Finset.mem_Ico.mp hr
    have hpBand' := mem_smallPrimeBandPrimes.mp hpBand
    apply mem_shallowSmallPrimeTailPrimes.mpr
    refine ⟨mem_smallPrimeTailPrimes.mpr
      ⟨hpBand'.1, hpBand'.2.1, hpBand'.2.2.1, ?_⟩, ?_⟩
    · simpa [hpBand'.2.2.2] using hr'.1
    · simpa [hpBand'.2.2.2] using hr'.2

theorem smallPrimeBandPrimes_pairwiseDisjoint (X : ℕ) (s : Finset ℕ) :
    (s : Set ℕ).PairwiseDisjoint (smallPrimeBandPrimes X) := by
  intro r _hr t _ht hrt
  change Disjoint (smallPrimeBandPrimes X r) (smallPrimeBandPrimes X t)
  rw [Finset.disjoint_left]
  intro p hpr hpt
  have er := (mem_smallPrimeBandPrimes.mp hpr).2.2.2
  have et := (mem_smallPrimeBandPrimes.mp hpt).2.2.2
  exact hrt (er.symm.trans et)

theorem weighted_shallowSmallPrimeTail_sum_eq (X R J : ℕ) :
    (∑ p ∈ shallowSmallPrimeTailPrimes X R J,
      (2 / 3 : ℝ) ^ smallPrimeDepth p X * (p : ℝ)⁻¹) =
      ∑ r ∈ Finset.Ico R J,
        (2 / 3 : ℝ) ^ r * smallPrimeBandMass X r := by
  rw [shallowSmallPrimeTailPrimes_eq_biUnion,
    Finset.sum_biUnion (smallPrimeBandPrimes_pairwiseDisjoint X
      (Finset.Ico R J))]
  apply Finset.sum_congr rfl
  intro r hr
  calc
    (∑ p ∈ smallPrimeBandPrimes X r,
        (2 / 3 : ℝ) ^ smallPrimeDepth p X * (p : ℝ)⁻¹) =
        ∑ p ∈ smallPrimeBandPrimes X r,
          (2 / 3 : ℝ) ^ r * (p : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [(mem_smallPrimeBandPrimes.mp hp).2.2.2]
    _ = (2 / 3 : ℝ) ^ r * smallPrimeBandMass X r := by
      unfold smallPrimeBandMass
      rw [Finset.mul_sum]

theorem smallPrimeTailPrimes_shallow_union_deep (X R J : ℕ) :
    smallPrimeTailPrimes X R =
      shallowSmallPrimeTailPrimes X R J ∪
        deepSmallPrimeTailPrimes X R J := by
  ext p
  simp only [mem_smallPrimeTailPrimes, mem_shallowSmallPrimeTailPrimes,
    mem_deepSmallPrimeTailPrimes, Finset.mem_union]
  constructor
  · intro hp
    by_cases hd : smallPrimeDepth p X < J
    · exact Or.inl ⟨hp, hd⟩
    · exact Or.inr ⟨hp, Nat.le_of_not_gt hd⟩
  · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp

theorem shallow_deep_disjoint (X R J : ℕ) :
    Disjoint (shallowSmallPrimeTailPrimes X R J)
      (deepSmallPrimeTailPrimes X R J) := by
  rw [Finset.disjoint_left]
  intro p hs hd
  have hs' := (mem_shallowSmallPrimeTailPrimes.mp hs).2
  have hd' := (mem_deepSmallPrimeTailPrimes.mp hd).2
  omega

theorem deepSmallPrimeTailMass_le (X R J : ℕ) :
    (∑ p ∈ deepSmallPrimeTailPrimes X R J,
      (2 / 3 : ℝ) ^ smallPrimeDepth p X * (p : ℝ)⁻¹) ≤
      (2 / 3 : ℝ) ^ J * reciprocalPrimeSum (Nat.sqrt X) := by
  calc
    (∑ p ∈ deepSmallPrimeTailPrimes X R J,
        (2 / 3 : ℝ) ^ smallPrimeDepth p X * (p : ℝ)⁻¹) ≤
        ∑ p ∈ deepSmallPrimeTailPrimes X R J,
          (2 / 3 : ℝ) ^ J * (p : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one (by norm_num) (by norm_num)
          (mem_deepSmallPrimeTailPrimes.mp hp).2)
        (by positivity)
    _ = (2 / 3 : ℝ) ^ J *
        ∑ p ∈ deepSmallPrimeTailPrimes X R J, (p : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ (2 / 3 : ℝ) ^ J * reciprocalPrimeSum (Nat.sqrt X) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) J)
      unfold reciprocalPrimeSum
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hpTail := (mem_deepSmallPrimeTailPrimes.mp hp).1
        have hpTail' := mem_smallPrimeTailPrimes.mp hpTail
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hpTail'.2.2.1⟩
      · intro p _ _
        positivity

theorem weightedSmallPrimeTailMass_le_shallow_add_deep
    (X R J : ℕ) :
    weightedSmallPrimeTailMass X R ≤
      (∑ r ∈ Finset.Ico R J,
        (2 / 3 : ℝ) ^ r * smallPrimeBandMass X r) +
        (2 / 3 : ℝ) ^ J * reciprocalPrimeSum (Nat.sqrt X) := by
  unfold weightedSmallPrimeTailMass
  rw [smallPrimeTailPrimes_shallow_union_deep X R J,
    Finset.sum_union (shallow_deep_disjoint X R J),
    weighted_shallowSmallPrimeTail_sum_eq]
  exact add_le_add le_rfl (deepSmallPrimeTailMass_le X R J)

/-! ## The ledger tail is controlled by the weighted prime mass -/

/-- The local obstruction itself excludes `p = 2`, so the corresponding
fiber is literally empty. -/
theorem localHigherPowerFiber_two_eq_empty (X : ℕ) (L : Branch) :
    localHigherPowerFiber X L 2 1 = ∅ := by
  ext x
  simp [mem_localHigherPowerFiber, LocalBranchObstruction]

/-- The factor `12` is exactly `4` branches times the factor `3` in the
padded complete-block estimate. -/
theorem normalizedSmallPrimeDepthTailWitnessCount_le_weightedMass
    {X R : ℕ} (hX : 0 < X) :
    normalizedSmallPrimeDepthTailWitnessCount R X ≤
      12 * weightedSmallPrimeTailMass X R := by
  have hcard := localSmallPrimeDepthTailWitnesses_card_le_keys X R
  have hcast :
      ((localSmallPrimeDepthTailWitnessesUpTo X R).card : ℝ) ≤
        ((smallPrimeKeys X (smallPrimeTailPrimes X R)).card : ℝ) := by
    exact_mod_cast hcard
  unfold normalizedSmallPrimeDepthTailWitnessCount
  calc
    ((localSmallPrimeDepthTailWitnessesUpTo X R).card : ℝ) / (X : ℝ) ≤
        ((smallPrimeKeys X (smallPrimeTailPrimes X R)).card : ℝ) /
          (X : ℝ) := by
      exact div_le_div_of_nonneg_right hcast (by positivity)
    _ = ∑ L : Branch, ∑ p ∈ smallPrimeTailPrimes X R,
          ((localHigherPowerFiber X L p 1).card : ℝ) / (X : ℝ) := by
      rw [smallPrimeKeys_card]
      push_cast
      simp only [Finset.sum_div]
    _ ≤ ∑ L : Branch, ∑ p ∈ smallPrimeTailPrimes X R,
          3 * ((2 / 3 : ℝ) ^ smallPrimeDepth p X * (p : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro L _hL
      apply Finset.sum_le_sum
      intro p hpTail
      have hpTail' := mem_smallPrimeTailPrimes.mp hpTail
      by_cases hp2 : p = 2
      · subst p
        rw [localHigherPowerFiber_two_eq_empty]
        simp only [card_empty, CharP.cast_eq_zero, zero_div, Nat.cast_ofNat,
          Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, inv_pos,
          mul_nonneg_iff_of_pos_right, ge_iff_le]
        positivity
      · have hfiber := localSmallPrimeFiber_normalized_le_uniform
            hX hpTail'.2.2.1 hp2 hpTail'.2.1
            (r := smallPrimeDepth p X) rfl (L := L)
        calc
          ((localHigherPowerFiber X L p 1).card : ℝ) / (X : ℝ) ≤
              (3 / (p : ℝ)) *
                (2 / 3 : ℝ) ^ smallPrimeDepth p X := hfiber
          _ = 3 * ((2 / 3 : ℝ) ^ smallPrimeDepth p X *
                (p : ℝ)⁻¹) := by ring
    _ = 12 * weightedSmallPrimeTailMass X R := by
      unfold weightedSmallPrimeTailMass
      rw [← Finset.mul_sum]
      have hbranch : Fintype.card Branch = 4 := by decide
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hbranch]
      ring

/-! ## A single uniform finite-depth tail bound -/

/-- If `r` lies below the moving deepest-band cutoff, then the lower
endpoint of its real prime band is at least two.  The proof keeps the
natural floor/logarithm bookkeeping explicit: `r + 2 ≤ log₃(√X)` gives
`2^(r+2) ≤ X`. -/
theorem fixedDepthPrimeBandLower_ge_two_of_lt_movingDepth
    {X r : ℕ} (hX : 9 ≤ X)
    (hr : r < movingDepthLog X - 1) :
    2 ≤ fixedDepthPrimeBandLower r (X : ℝ) := by
  let N : ℕ := Nat.sqrt X
  let m : ℕ := Nat.log 3 N
  have hNpos : 0 < N := by
    dsimp only [N]
    exact Nat.sqrt_pos.2 (by omega)
  have hr' : r < m - 1 := by
    simpa only [movingDepthLog, N, m] using hr
  have hrm : r + 2 ≤ m := by
    omega
  have hpowLog : 3 ^ m ≤ N := by
    exact Nat.pow_log_le_self 3 hNpos.ne'
  have hpowTwo : 2 ^ (r + 2) ≤ X := by
    calc
      2 ^ (r + 2) ≤ 3 ^ (r + 2) :=
        Nat.pow_le_pow_left (by norm_num) _
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hrm
      _ ≤ N := hpowLog
      _ ≤ X := by
        dsimp only [N]
        exact Nat.sqrt_le_self X
  unfold fixedDepthPrimeBandLower
  rw [Real.le_rpow_inv_iff_of_pos (by norm_num : (0 : ℝ) ≤ 2)
    (by positivity : (0 : ℝ) ≤ X)
    (by positivity : (0 : ℝ) < (r + 2 : ℕ))]
  rw [Real.rpow_natCast]
  exact_mod_cast hpowTwo

/-- Finite, uniform equation (45): every residual depth is paid for by
the summable Mertens main tail, the quantitative Mertens error, or the
single deepest moving band. -/
theorem weightedSmallPrimeTailMass_le_majorant
    {X R : ℕ} (hX : 9 ≤ X) :
    weightedSmallPrimeTailMass X R ≤
      uniformDepthMainTail R + uniformMertensErrorMajorant X +
        deepestBandMajorant X := by
  let J : ℕ := movingDepthLog X - 1
  have hX1 : 1 < X := by omega
  have hband :
      (∑ r ∈ Finset.Ico R J,
        (2 / 3 : ℝ) ^ r * smallPrimeBandMass X r) ≤
      ∑ r ∈ Finset.Ico R J,
        (2 / 3 : ℝ) ^ r *
          fixedDepthReciprocalPrimeBand r (X : ℝ) := by
    apply Finset.sum_le_sum
    intro r hr
    exact mul_le_mul_of_nonneg_left
      (smallPrimeBandMass_le_fixedDepthReciprocalPrimeBand hX1)
      (pow_nonneg (by norm_num) r)
  have hMertens := weightedFixedDepthBand_sum_le_main_add_error
    (Finset.Ico R J) hX1 (fun r hr ↦
      fixedDepthPrimeBandLower_ge_two_of_lt_movingDepth hX
        (by simpa only [J] using (Finset.mem_Ico.mp hr).2))
  have hmain := uniformDepthMain_sum_Ico_le_tail R J
  calc
    weightedSmallPrimeTailMass X R ≤
        (∑ r ∈ Finset.Ico R J,
          (2 / 3 : ℝ) ^ r * smallPrimeBandMass X r) +
          (2 / 3 : ℝ) ^ J * reciprocalPrimeSum (Nat.sqrt X) :=
      weightedSmallPrimeTailMass_le_shallow_add_deep X R J
    _ ≤ (∑ r ∈ Finset.Ico R J,
          (2 / 3 : ℝ) ^ r *
            fixedDepthReciprocalPrimeBand r (X : ℝ)) +
          (2 / 3 : ℝ) ^ J * reciprocalPrimeSum (Nat.sqrt X) :=
      add_le_add hband le_rfl
    _ ≤ ((∑ r ∈ Finset.Ico R J, uniformDepthMainTerm r) +
          uniformMertensErrorMajorant X) + deepestBandMajorant X := by
      exact add_le_add hMertens (by rfl)
    _ ≤ uniformDepthMainTail R + uniformMertensErrorMajorant X +
          deepestBandMajorant X := by
      exact add_le_add (add_le_add hmain le_rfl) le_rfl

/-- Quantified ledger-level tail bound consumed by the limsup-series
assembly. -/
theorem normalizedSmallPrimeDepthTailWitnessCount_le_majorant
    {X R : ℕ} (hX : 9 ≤ X) :
    normalizedSmallPrimeDepthTailWitnessCount R X ≤
      12 * (uniformDepthMainTail R + uniformMertensErrorMajorant X +
        deepestBandMajorant X) := by
  exact (normalizedSmallPrimeDepthTailWitnessCount_le_weightedMass
    (by omega : 0 < X)).trans (mul_le_mul_of_nonneg_left
      (weightedSmallPrimeTailMass_le_majorant hX) (by norm_num))

/-- The explicit analytic majorant for the normalized residual ledger. -/
def smallPrimeDepthTailMajorant (R X : ℕ) : ℝ :=
  12 * (uniformDepthMainTail R + uniformMertensErrorMajorant X +
    deepestBandMajorant X)

theorem tendsto_smallPrimeDepthTailMajorant (R : ℕ) :
    Tendsto (smallPrimeDepthTailMajorant R) atTop
      (nhds (12 * uniformDepthMainTail R)) := by
  have hconst : Tendsto (fun _ : ℕ ↦ uniformDepthMainTail R) atTop
      (nhds (uniformDepthMainTail R)) := tendsto_const_nhds
  have hsum := (hconst.add
    tendsto_uniformMertensErrorMajorant_zero).add
      tendsto_deepestBandMajorant_zero
  have hmul := hsum.const_mul 12
  simpa only [smallPrimeDepthTailMajorant, add_zero, mul_zero] using! hmul

theorem eventually_normalizedSmallPrimeDepthTailWitnessCount_le_majorant
    (R : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      normalizedSmallPrimeDepthTailWitnessCount R X ≤
        smallPrimeDepthTailMajorant R X := by
  filter_upwards [eventually_ge_atTop 9] with X hX
  exact normalizedSmallPrimeDepthTailWitnessCount_le_majorant hX

theorem normalizedSmallPrimeDepthTailWitnessCount_isBoundedUnder
    (R : ℕ) :
    IsBoundedUnder (· ≤ ·) atTop
      (normalizedSmallPrimeDepthTailWitnessCount R) := by
  rcases (tendsto_smallPrimeDepthTailMajorant R).isBoundedUnder_le.eventually_le
    with ⟨C, hC⟩
  apply isBoundedUnder_of_eventually_le (a := C)
  filter_upwards
    [eventually_normalizedSmallPrimeDepthTailWitnessCount_le_majorant R,
      hC] with X htail hmajor
  exact htail.trans hmajor

/-- Uniform limsup tail estimate, with no fixed-depth Fourier input. -/
theorem limsup_normalizedSmallPrimeDepthTailWitnessCount_le (R : ℕ) :
    limsup (normalizedSmallPrimeDepthTailWitnessCount R) atTop ≤
      12 * uniformDepthMainTail R := by
  have htailCob : IsCoboundedUnder (· ≤ ·) atTop
      (normalizedSmallPrimeDepthTailWitnessCount R) :=
    isCoboundedUnder_le_of_le atTop
      (normalizedSmallPrimeDepthTailWitnessCount_nonneg R)
  have hmajorBdd :=
    (tendsto_smallPrimeDepthTailMajorant R).isBoundedUnder_le
  calc
    limsup (normalizedSmallPrimeDepthTailWitnessCount R) atTop ≤
        limsup (smallPrimeDepthTailMajorant R) atTop :=
      limsup_le_limsup
        (eventually_normalizedSmallPrimeDepthTailWitnessCount_le_majorant R)
        htailCob hmajorBdd
    _ = 12 * uniformDepthMainTail R :=
      (tendsto_smallPrimeDepthTailMajorant R).limsup_eq

/-! ## Global assembly constants -/

/-- Four branches times the fixed-depth budget term. -/
def smallPrimeDepthBudgetTerm (r : ℕ) : ℝ :=
  4 * densityBudgetTerm r

theorem smallPrimeDepthBudgetTerm_nonneg (r : ℕ) :
    0 ≤ smallPrimeDepthBudgetTerm r := by
  exact mul_nonneg (by norm_num) (densityBudgetTerm_nonneg r)

theorem smallPrimeDepthBudgetTerm_summable :
    Summable smallPrimeDepthBudgetTerm := by
  exact densityBudgetTerm_summable.mul_left 4

theorem tsum_smallPrimeDepthBudgetTerm :
    (∑' r : ℕ, smallPrimeDepthBudgetTerm r) =
      4 * densityBudgetSeries := by
  unfold smallPrimeDepthBudgetTerm densityBudgetSeries
  rw [tsum_mul_left]

theorem tendsto_smallPrimeDepthTailBudget_zero :
    Tendsto (fun R : ℕ ↦ 12 * uniformDepthMainTail R) atTop
      (nhds 0) := by
  simpa only [mul_zero] using
    tendsto_uniformDepthMainTail_zero.const_mul 12

/-- Every exact-depth normalized ledger is bounded above. -/
theorem normalizedSmallPrimeDepthWitnessCount_isBoundedUnder (r : ℕ) :
    IsBoundedUnder (· ≤ ·) atTop
      (normalizedSmallPrimeDepthWitnessCount r) := by
  by_cases hr0 : r = 0
  · subst r
    apply isBoundedUnder_of_eventually_le (a := 0)
    exact Eventually.of_forall fun X ↦ by
      simp
  · have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
    have hlim := (tendsto_fixedDepthAnalyticMajorant r hr).const_mul 4
    rcases hlim.isBoundedUnder_le.eventually_le with ⟨C, hC⟩
    apply isBoundedUnder_of_eventually_le (a := C)
    filter_upwards
      [eventually_normalizedSmallPrimeDepthWitnessCount_le_majorant r hr,
        hC] with X hcount hmajor
    exact hcount.trans hmajor

/-- Fixed-depth limsup estimate, including the absent depth-zero boundary. -/
theorem limsup_normalizedSmallPrimeDepthWitnessCount_le (r : ℕ) :
    limsup (normalizedSmallPrimeDepthWitnessCount r) atTop ≤
      smallPrimeDepthBudgetTerm r := by
  by_cases hr0 : r = 0
  · subst r
    have hfun : normalizedSmallPrimeDepthWitnessCount 0 =
        (fun _ : ℕ ↦ (0 : ℝ)) := by
      funext X
      exact normalizedSmallPrimeDepthWitnessCount_zero X
    rw [hfun]
    have hconst : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds
    rw [hconst.limsup_eq]
    simp [smallPrimeDepthBudgetTerm, densityBudgetTerm]
  · have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
    have hlim := (tendsto_fixedDepthAnalyticMajorant r hr).const_mul 4
    have hcountCob : IsCoboundedUnder (· ≤ ·) atTop
        (normalizedSmallPrimeDepthWitnessCount r) :=
      isCoboundedUnder_le_of_le atTop
        (normalizedSmallPrimeDepthWitnessCount_nonneg r)
    calc
      limsup (normalizedSmallPrimeDepthWitnessCount r) atTop ≤
          limsup (fun X : ℕ ↦ 4 * fixedDepthAnalyticMajorant r X) atTop :=
        limsup_le_limsup
          (eventually_normalizedSmallPrimeDepthWitnessCount_le_majorant r hr)
          hcountCob hlim.isBoundedUnder_le
      _ = 4 * (fixedDepthBaseDensity r *
          fixedDepthPrimeBandMainTerm r) := hlim.limsup_eq
      _ = smallPrimeDepthBudgetTerm r := by
        simp only [smallPrimeDepthBudgetTerm, densityBudgetTerm, hr0,
          if_false, fixedDepthBaseDensity, fixedDepthPrimeBandMainTerm]

/-- Boundedness of the entire normalized small-prime ledger already follows
from the depth-zero tail majorant; it does not depend on the sharp
fixed-depth Fourier estimate. -/
theorem normalizedSmallPrimeWitnessCount_isBoundedUnder :
    IsBoundedUnder (· ≤ ·) atTop normalizedSmallPrimeWitnessCount := by
  rcases
      (normalizedSmallPrimeDepthTailWitnessCount_isBoundedUnder 0).eventually_le
    with ⟨C, hC⟩
  apply isBoundedUnder_of_eventually_le (a := C)
  filter_upwards [hC] with X htail
  have hdecomp := normalizedSmallPrimeWitnessCount_le_depth_sum_add_tail X 0
  have htotalTail : normalizedSmallPrimeWitnessCount X ≤
      normalizedSmallPrimeDepthTailWitnessCount 0 X := by
    simpa using hdecomp
  exact htotalTail.trans htail

/-- Full small-prime estimate: the fixed-depth Fourier bounds and the
uniform moving-depth tail assemble to the exact four-branch budget series. -/
theorem limsup_normalizedSmallPrimeWitnessCount_le :
    limsup normalizedSmallPrimeWitnessCount atTop ≤
      4 * densityBudgetSeries := by
  have hseries := limsup_le_tsum_of_finite_depth_and_tail
    (f := atTop)
    (term := smallPrimeDepthBudgetTerm)
    (total := normalizedSmallPrimeWitnessCount)
    (band := normalizedSmallPrimeDepthWitnessCount)
    (tail := normalizedSmallPrimeDepthTailWitnessCount)
    smallPrimeDepthBudgetTerm_nonneg
    smallPrimeDepthBudgetTerm_summable
    normalizedSmallPrimeWitnessCount_nonneg
    normalizedSmallPrimeDepthWitnessCount_nonneg
    normalizedSmallPrimeDepthWitnessCount_isBoundedUnder
    limsup_normalizedSmallPrimeDepthWitnessCount_le
    normalizedSmallPrimeDepthTailWitnessCount_nonneg
    normalizedSmallPrimeDepthTailWitnessCount_isBoundedUnder
    (fun R : ℕ ↦ 12 * uniformDepthMainTail R)
    tendsto_smallPrimeDepthTailBudget_zero
    limsup_normalizedSmallPrimeDepthTailWitnessCount_le
    (fun R ↦ Eventually.of_forall fun X ↦
      normalizedSmallPrimeWitnessCount_le_depth_sum_add_tail X R)
  simpa only [tsum_smallPrimeDepthBudgetTerm] using hseries

end

end Erdos730.SmallPrimeEvents
