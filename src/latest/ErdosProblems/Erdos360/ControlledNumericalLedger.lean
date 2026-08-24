/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.PrimeRandomControlledEventually
import ErdosProblems.Erdos360.ControlledParameterChoices

/-!
# Erdős 360: the truthful controlled numerical ledger

`CFPControlledPrimeParameterLedger` historically bundled the numerical
random/Lev estimates with `CFPPrimePoolOrdinaryNumerics`.  The latter contains
the false coarse scale inequality and is not a numerical consequence of the
prime-structured parameters.

This file separates the two logically independent inputs.  The record
`CFPControlledPrimeNumericalLedger` contains exactly the valid extraction,
random-selection, and Lev-side inequalities.  Ordinary subset-sum growth is
supplied separately by a local callback.  The callback retains the complete
extraction context, so a future adaptive proof may use the prime normal form
instead of pretending that range and diversity alone suffice.
-/

namespace Erdos360

open Filter

attribute [local instance] Classical.propDecidable

/-- The local ordinary-growth conclusion required for one extracted set.
This definition contains no claim that range and diversity alone imply the
conclusion; it merely records the result which the structured adaptive proof
must provide in its full source context. -/
def CFPControlledPrimeLocalOrdinaryCompletion
    (n y ell d : ℕ) (Z : Finset ℕ) : Prop :=
  ∀ P : Finset ℕ,
    P ⊆ lowerPart Z (Z.card % (8 * ell)) →
    P.card = primeRandomPoolSize Z.card ell →
    DiverseSampling.DiverseNat P (primeRandomPoolDiversity y ell) →
    Nonempty (CFPOrdinaryGrowthCertificate P
      (primeRandomNzero y Z.card ell d)
      (primeRandomDiameter y Z.card ell d))

/-- Exact numerical ledger after controlled extraction, with the false
ordinary-scale field removed. -/
structure CFPControlledPrimeNumericalLedger
    (n y U B L M Q ell : ℕ) : Prop where
  ell_pos : 0 < ell
  residual_large : 12 * ell ^ 2 ≤ L - (8 * ell - 1)
  U_pos : 0 < U
  B_pos : 0 < B
  B_cut : B ≤ y / U
  Q_pos : 0 < Q
  loss_room : Q + L * Nat.log 2 B ≤ M
  post : ∀ d z : ℕ, 0 < d → d ≤ U → Q ≤ z → z ≤ M →
    (L - (8 * ell - 1)) +
        (2 * y / d) / (B / d + 1) + (8 * ell - 1) ≤ Q ∧
    (∀ j < ell,
      RandomDiversity.exactSplitFailureMass (2 * y / d)
        (M / (8 * ell)) (8 * ell - j)
        (RandomDiversity.residualDiversity
          (L - (8 * ell - 1)) (8 * ell) j) < 1) ∧
    (∀ j < ell,
      primeRandomPoolDiversity y ell ≤
        RandomDiversity.residualDiversity
          (L - (8 * ell - 1)) (8 * ell) j /
            (2 * (8 * ell - j))) ∧
    3 ≤ primeRandomNzero y z ell d ∧
    2 * ((primeRandomDiameter y z ell d - 1) ⌈/⌉
      (primeRandomNzero y z ell d - 2)) ≤ ell ∧
    2 * y ≤ ell * (primeRandomNzero y z ell d - 1) + 1 ∧
    ell * (M / (8 * ell)) * (2 * y / d) < n / d ∧
    n / d ≤ (y / d + 1) * (Q - ell * (M / (8 * ell)))

/-- The general controlled constructor specialized to the prime parameters,
but with ordinary growth accepted as an independent local result rather than
manufactured from the false coarse scale inequality. -/
noncomputable def controlledPrimeRandomPreLevInput_of_numerical_post
    {n colors y B L M Q ell : ℕ} {Y : Finset (BelowTarget n)}
    {c : BelowTarget n → Fin colors} {i : Fin colors}
    {W Z : Finset ℕ} {d : ℕ}
    (hell : 0 < ell)
    (hk : 12 * ell ^ 2 ≤ L - (8 * ell - 1))
    (hY : ∀ x ∈ Y, y < x.1 ∧ x.1 ≤ 2 * y)
    (hW : W ⊆ integerColorClass Y c i) (hWcard : W.card = M)
    (hd : 0 < d) (hdB : d ≤ B)
    (hscale : ∀ z ∈ Z, d * z ∈ W)
    (hloss : W.card - Z.card ≤ L * Nat.log 2 B)
    (hdiverse : ∀ e : ℕ, 1 < e → d * e ≤ B →
      L ≤ (Z.filter fun z ↦ ¬e ∣ z).card)
    (hlossRoom : Q + L * Nat.log 2 B ≤ M)
    (hlarge : (L - (8 * ell - 1)) +
      (2 * y / d) / (B / d + 1) + (8 * ell - 1) ≤ Q)
    (hprobability : ∀ j < ell,
      RandomDiversity.exactSplitFailureMass (2 * y / d)
        (M / (8 * ell)) (8 * ell - j)
        (RandomDiversity.residualDiversity
          (L - (8 * ell - 1)) (8 * ell) j) < 1)
    (hdiversity : ∀ j < ell,
      primeRandomPoolDiversity y ell ≤
        RandomDiversity.residualDiversity
          (L - (8 * ell - 1)) (8 * ell) j /
            (2 * (8 * ell - j)))
    (hordinary : CFPControlledPrimeLocalOrdinaryCompletion n y ell d Z)
    (hnzero : 3 ≤ primeRandomNzero y Z.card ell d)
    (hlev : 2 * ((primeRandomDiameter y Z.card ell d - 1) ⌈/⌉
      (primeRandomNzero y Z.card ell d - 2)) ≤ ell)
    (hwidth : 2 * y ≤
      ell * (primeRandomNzero y Z.card ell d - 1) + 1)
    (hsum : ell * (M / (8 * ell)) * (2 * y / d) < n / d)
    (hunused : n / d ≤
      (y / d + 1) * (Q - ell * (M / (8 * ell)))) :
    CFPRandomPreLevInput n d y Z := by
  have hscaleClass : ∀ z ∈ Z,
      d * z ∈ integerColorClass Y c i := fun z hz ↦ hW (hscale z hz)
  have hresidualPos : 0 < L - (8 * ell - 1) :=
    (by positivity : 0 < 12 * ell ^ 2).trans_le hk
  have hreserve : 8 * ell - 1 ≤ L :=
    (Nat.sub_pos_iff_lt.mp hresidualPos).le
  have hkL : (L - (8 * ell - 1)) + (8 * ell - 1) ≤ L := by
    rw [Nat.sub_add_cancel hreserve]
  have hcellCount : ell + 2 ≤ 8 * ell := by omega
  apply controlledRandomPreLevInput
    (K := 0) (h := 8 * ell) (ell := ell)
    (k := L - (8 * ell - 1))
    (diversity := primeRandomPoolDiversity y ell)
    (nzero := primeRandomNzero y Z.card ell d)
    (diameter := primeRandomDiameter y Z.card ell d)
    hY hW hWcard hd hdB (by positivity) hscale
    (by simpa using hloss) (by simpa using hdiverse)
    (by simpa using hlossRoom) hkL hlarge hcellCount
    hprobability hdiversity
  · exact hordinary
  · exact hnzero
  · exact hlev
  · exact hwidth
  · exact hsum
  · exact hunused

/-- Ordinary growth in the full source context.  The two divisor conclusions
are explicitly supplied to the callback, permitting use of the retained
prime factorization after extraction. -/
def CFPControlledPrimeOrdinarySourceCompletion
    (n colors y U B L M ell : ℕ) (Y : Finset (BelowTarget n)) : Prop :=
  ∀ (c : BelowTarget n → Fin colors) (i : Fin colors)
      (W : Finset ℕ) (d : ℕ) (Z : Finset ℕ),
    W ⊆ integerColorClass Y c i → W.card = M →
    0 < d → d ≤ B →
    (∀ z ∈ Z, d * z ∈ W) →
    W.card - Z.card ≤ L * Nat.log 2 B →
    (∀ e : ℕ, 1 < e → d * e ≤ B →
      L ≤ (Z.filter fun z ↦ ¬e ∣ z).card) →
    d ∣ n → d ≤ U →
    CFPControlledPrimeLocalOrdinaryCompletion n y ell d Z

/-- The numerical ledger and the separate structured ordinary callback
produce the existing exact controlled source completion. -/
theorem controlledRandomTestSetSource_of_numericalLedger
    {n colors y U B L M Q ell : ℕ} {hy : 2 * y < n}
    (hnum : CFPControlledPrimeNumericalLedger n y U B L M Q ell)
    (hordinary : CFPControlledPrimeOrdinarySourceCompletion
      n colors y U B L M ell
        (primeStructuredBelowTarget n y U hy)) :
    CFPControlledRandomTestSetSourceCompletion n colors y U B L M
      (primeStructuredBelowTarget n y U hy) := by
  intro c i W d Z hW hWcard hd hdB hscale hloss hdiverse
  have hZupper : Z.card ≤ M := by
    simpa [hWcard] using card_le_of_positive_scale_subset hd hscale
  have hZlower : Q ≤ Z.card :=
    extracted_card_lower_of_controlled_loss hd hWcard hscale hloss
      hnum.loss_room
  have hZnonempty : Z.Nonempty :=
    Finset.card_pos.mp (hnum.Q_pos.trans_le hZlower)
  have hdData := extracted_scale_dvd_target_and_le_cutoff
    hnum.B_cut hd hdB hW hscale hZnonempty
  rcases hnum.post d Z.card hd hdData.2 hZlower hZupper with
    ⟨hlarge, hprobability, hdiversity, hnzero, hlev, hwidth,
      hsum, hunused⟩
  have hlocal := hordinary c i W d Z hW hWcard hd hdB hscale
    hloss hdiverse hdData.1 hdData.2
  refine ⟨hdData.1, ⟨?_⟩⟩
  exact controlledPrimeRandomPreLevInput_of_numerical_post
    hnum.ell_pos hnum.residual_large
    (fun x hx ↦ primeStructuredBelowTarget_dyadic hx)
    hW hWcard hd hdB hscale hloss hdiverse hnum.loss_room
    hlarge hprobability hdiversity hlocal hnzero hlev hwidth hsum hunused

/-! ## Canonical eventual target and its exact remaining estimates -/

/-- The canonical instance of the truthful ledger. -/
def CanonicalControlledPrimeNumericalLedger (n : ℕ) : Prop :=
  let y := initialLowerY n (lowerColorCount 1 n)
  CFPControlledPrimeNumericalLedger n y
    (controlledPrimeU n) (controlledPrimeB n y) (controlledPrimeL y)
    (controlledPrimeClassCapTwelve n y)
    (controlledPrimeExtractedFloorTwelve n y) controlledPrimeEll

/-- The eight post-extraction estimates that remain after the elementary
choice numerics have been discharged.  This is an audit record, not an
ordinary-growth assumption. -/
structure ControlledPrimePostEstimates (n y : ℕ) : Prop where
  residual_large : 12 * controlledPrimeEll ^ 2 ≤
    controlledPrimeL y - (8 * controlledPrimeEll - 1)
  large : ∀ d z : ℕ, 0 < d → d ≤ controlledPrimeU n →
    controlledPrimeExtractedFloorTwelve n y ≤ z →
    z ≤ controlledPrimeClassCapTwelve n y →
    (controlledPrimeL y - (8 * controlledPrimeEll - 1)) +
        (2 * y / d) / (controlledPrimeB n y / d + 1) +
          (8 * controlledPrimeEll - 1) ≤
      controlledPrimeExtractedFloorTwelve n y
  probability : ∀ d z : ℕ, 0 < d → d ≤ controlledPrimeU n →
    controlledPrimeExtractedFloorTwelve n y ≤ z →
    z ≤ controlledPrimeClassCapTwelve n y →
    ∀ j < controlledPrimeEll,
      RandomDiversity.exactSplitFailureMass (2 * y / d)
        (controlledPrimeClassCapTwelve n y /
          (8 * controlledPrimeEll)) (8 * controlledPrimeEll - j)
        (RandomDiversity.residualDiversity
          (controlledPrimeL y - (8 * controlledPrimeEll - 1))
          (8 * controlledPrimeEll) j) < 1
  diversity : ∀ d z : ℕ, 0 < d → d ≤ controlledPrimeU n →
    controlledPrimeExtractedFloorTwelve n y ≤ z →
    z ≤ controlledPrimeClassCapTwelve n y →
    ∀ j < controlledPrimeEll,
      primeRandomPoolDiversity y controlledPrimeEll ≤
        RandomDiversity.residualDiversity
          (controlledPrimeL y - (8 * controlledPrimeEll - 1))
          (8 * controlledPrimeEll) j /
            (2 * (8 * controlledPrimeEll - j))
  nzero : ∀ d z : ℕ, 0 < d → d ≤ controlledPrimeU n →
    controlledPrimeExtractedFloorTwelve n y ≤ z →
    z ≤ controlledPrimeClassCapTwelve n y →
    3 ≤ primeRandomNzero y z controlledPrimeEll d
  lev : ∀ d z : ℕ, 0 < d → d ≤ controlledPrimeU n →
    controlledPrimeExtractedFloorTwelve n y ≤ z →
    z ≤ controlledPrimeClassCapTwelve n y →
    2 * ((primeRandomDiameter y z controlledPrimeEll d - 1) ⌈/⌉
      (primeRandomNzero y z controlledPrimeEll d - 2)) ≤
        controlledPrimeEll
  width : ∀ d z : ℕ, 0 < d → d ≤ controlledPrimeU n →
    controlledPrimeExtractedFloorTwelve n y ≤ z →
    z ≤ controlledPrimeClassCapTwelve n y →
    2 * y ≤ controlledPrimeEll *
      (primeRandomNzero y z controlledPrimeEll d - 1) + 1
  sum : ∀ d z : ℕ, 0 < d → d ≤ controlledPrimeU n →
    controlledPrimeExtractedFloorTwelve n y ≤ z →
    z ≤ controlledPrimeClassCapTwelve n y →
    controlledPrimeEll *
      (controlledPrimeClassCapTwelve n y /
        (8 * controlledPrimeEll)) * (2 * y / d) < n / d
  unused : ∀ d z : ℕ, 0 < d → d ≤ controlledPrimeU n →
    controlledPrimeExtractedFloorTwelve n y ≤ z →
    z ≤ controlledPrimeClassCapTwelve n y →
    n / d ≤ (y / d + 1) *
      (controlledPrimeExtractedFloorTwelve n y -
        controlledPrimeEll *
          (controlledPrimeClassCapTwelve n y /
            (8 * controlledPrimeEll)))

/-! The following reductions show which parts of the post record are purely
finite arithmetic and which scalar estimates the eventual proof must supply. -/

lemma controlledPrime_residual_large_of_root
    {y : ℕ} (hroot : 12 * controlledPrimeEll ^ 2 ≤ fourthRootCeil y) :
    12 * controlledPrimeEll ^ 2 ≤
      controlledPrimeL y - (8 * controlledPrimeEll - 1) := by
  rw [show 8 * controlledPrimeEll = controlledPrimeCells by rfl,
    controlledPrimeL_sub_reserve]
  exact hroot.trans (Nat.le_mul_of_pos_left _ (by norm_num))

/-- The entire diversity ledger is automatic from the million-fold
fourth-root reserve; it requires no asymptotic estimate beyond residual
positivity. -/
lemma controlledPrime_canonical_diversity_ledger
    {y : ℕ}
    (hres : 12 * controlledPrimeEll ^ 2 ≤
      controlledPrimeL y - (8 * controlledPrimeEll - 1)) :
    ∀ j < controlledPrimeEll,
      primeRandomPoolDiversity y controlledPrimeEll ≤
        RandomDiversity.residualDiversity
          (controlledPrimeL y - (8 * controlledPrimeEll - 1))
          (8 * controlledPrimeEll) j /
            (2 * (8 * controlledPrimeEll - j)) := by
  apply controlledPrime_diversity_ledger
    (ell := controlledPrimeEll) (L := controlledPrimeL y)
  · norm_num [controlledPrimeEll]
  · exact hres
  · unfold primeRandomPoolDiversity
    rw [show 8 * controlledPrimeEll = controlledPrimeCells by rfl,
      controlledPrimeL_sub_reserve]
    norm_num [controlledPrimeEll]
    omega

/-- The divisor-dependent endpoint in the large-room field costs at most
`2*U`. -/
lemma controlledPrime_canonical_large_of_room
    {n y d : ℕ} (hn : 0 < n)
    (hroom : controlledPrimeL y + 2 * controlledPrimeU n ≤
      controlledPrimeExtractedFloorTwelve n y)
    (hd : 0 < d) :
    (controlledPrimeL y - (8 * controlledPrimeEll - 1)) +
        (2 * y / d) / (controlledPrimeB n y / d + 1) +
          (8 * controlledPrimeEll - 1) ≤
      controlledPrimeExtractedFloorTwelve n y := by
  have hend := controlled_endpoint_quotient_le_two_mul_U
    (n := n) (y := y) hn hd
  have hreserve : 8 * controlledPrimeEll - 1 ≤ controlledPrimeL y := by
    simpa [controlledPrimeCells] using controlledPrimeL_reserve y
  have hcancel :
      controlledPrimeL y - (8 * controlledPrimeEll - 1) +
          (8 * controlledPrimeEll - 1) = controlledPrimeL y :=
    Nat.sub_add_cancel hreserve
  omega

/-- The uniform split-probability family follows from its single global
exponential majorant. -/
lemma controlledPrime_canonical_probability_ledger
    {y M d : ℕ} (hd : 0 < d)
    (hres : 12 * controlledPrimeEll ^ 2 ≤
      controlledPrimeL y - (8 * controlledPrimeEll - 1))
    (hsmall : (4 : ℝ) * (M + 1) * (2 * y + 1) *
      Real.exp (- ((controlledPrimeL y -
          (8 * controlledPrimeEll - 1) : ℕ) : ℝ) /
        (1024 * (controlledPrimeEll : ℝ) ^ 2)) < 1) :
    ∀ j < controlledPrimeEll,
      RandomDiversity.exactSplitFailureMass (2 * y / d)
        (M / (8 * controlledPrimeEll))
        (8 * controlledPrimeEll - j)
        (RandomDiversity.residualDiversity
          (controlledPrimeL y - (8 * controlledPrimeEll - 1))
          (8 * controlledPrimeEll) j) < 1 := by
  exact controlledPrime_probability_ledger
    (ell := controlledPrimeEll) (L := controlledPrimeL y)
    (M := M) (y := y) (by norm_num [controlledPrimeEll]) hd
    hres hsmall

/-- Five units of ordinary mass already imply the complete Lev ratio for
the fixed pool count.  This removes `lev` as an independent eventual
estimate. -/
lemma controlledPrime_canonical_lev_of_five
    {y z d : ℕ} (hd : 0 < d)
    (hnzero : 5 ≤ primeRandomNzero y z controlledPrimeEll d) :
    2 * ((primeRandomDiameter y z controlledPrimeEll d - 1) ⌈/⌉
      (primeRandomNzero y z controlledPrimeEll d - 2)) ≤
        controlledPrimeEll := by
  let A := y * z
  have hbig : 0 < controlledPrimeEll ^ 2 * d := by
    norm_num [controlledPrimeEll]
    positivity
  have hsmall : 0 < 4 * controlledPrimeEll * d := by
    norm_num [controlledPrimeEll]
    positivity
  have hA : A <
      (A / (controlledPrimeEll ^ 2 * d) + 1) *
        (controlledPrimeEll ^ 2 * d) := by
    simpa [mul_comm] using Nat.lt_mul_div_succ A hbig
  have hdiameter : primeRandomDiameter y z controlledPrimeEll d ≤
      274877906944 * (primeRandomNzero y z controlledPrimeEll d + 1) := by
    unfold primeRandomDiameter
    apply (ceilDiv_le_iff_le_mul hsmall).2
    calc
      y * z ≤
          (y * z / (controlledPrimeEll ^ 2 * d) + 1) *
            (controlledPrimeEll ^ 2 * d) := hA.le
      _ = (4 * controlledPrimeEll * d) *
          (274877906944 *
            (primeRandomNzero y z controlledPrimeEll d + 1)) := by
        simp only [primeRandomNzero, controlledPrimeEll]
        ring
  have hden : 0 < primeRandomNzero y z controlledPrimeEll d - 2 := by
    omega
  have hratio :
      (primeRandomDiameter y z controlledPrimeEll d - 1) ⌈/⌉
          (primeRandomNzero y z controlledPrimeEll d - 2) ≤
            549755813888 := by
    apply (ceilDiv_le_iff_le_mul hden).2
    omega
  calc
    2 * ((primeRandomDiameter y z controlledPrimeEll d - 1) ⌈/⌉
        (primeRandomNzero y z controlledPrimeEll d - 2)) ≤
        2 * 549755813888 := Nat.mul_le_mul_left 2 hratio
    _ = controlledPrimeEll := by norm_num [controlledPrimeEll]

/-- A single product lower bound implies `nzero ≥ 5` uniformly for all
`d ≤ U` and `z ≥ Q`. -/
lemma controlledPrime_canonical_nzero_five_of_product
    {n y Q d z : ℕ} (hd : 0 < d) (hdU : d ≤ controlledPrimeU n)
    (hQz : Q ≤ z)
    (hmass : 5 * controlledPrimeEll ^ 2 * controlledPrimeU n ≤ y * Q) :
    5 ≤ primeRandomNzero y z controlledPrimeEll d := by
  unfold primeRandomNzero
  have hden : 0 < controlledPrimeEll ^ 2 * d := by
    norm_num [controlledPrimeEll]
    positivity
  apply (Nat.le_div_iff_mul_le hden).2
  calc
    5 * (controlledPrimeEll ^ 2 * d) ≤
        5 * (controlledPrimeEll ^ 2 * controlledPrimeU n) := by
      gcongr
    _ = 5 * controlledPrimeEll ^ 2 * controlledPrimeU n := by ring
    _ ≤ y * Q := hmass
    _ ≤ y * z := Nat.mul_le_mul_left y hQz

/-- A rounding-safe scalar room inequality implies the selected-sum field
uniformly in `d ≤ U`. -/
lemma controlledPrime_canonical_sum_of_room
    {n y M d : ℕ} (hd : 0 < d) (hdU : d ≤ controlledPrimeU n)
    (hroom : 2 *
        (controlledPrimeEll * (M / (8 * controlledPrimeEll))) * y +
          controlledPrimeU n ≤ n) :
    controlledPrimeEll * (M / (8 * controlledPrimeEll)) *
        (2 * y / d) < n / d := by
  let s := controlledPrimeEll * (M / (8 * controlledPrimeEll))
  have hleft : s * (2 * y / d) ≤ (2 * s * y) / d := by
    simpa [s, mul_assoc, mul_comm, mul_left_comm] using
      Nat.mul_div_le_mul_div_assoc s (2 * y) d
  have hquot : (2 * s * y) / d < n / d := by
    apply (Nat.div_lt_iff_lt_mul hd).2
    have hmod := Nat.mod_lt n hd
    have hdecomp : n % d + (n / d) * d = n := by
      simpa [mul_comm] using Nat.mod_add_div n d
    have hroom' : 2 * s * y + d ≤ n := by
      dsimp [s] at hroom ⊢
      omega
    omega
  exact hleft.trans_lt hquot

/-- The unused-mass field follows from the divisor-free scalar inequality
`n ≤ y * remaining`. -/
lemma controlledPrime_canonical_unused_of_room
    {n y M Q d : ℕ} (hd : 0 < d)
    (hroom : n ≤ y *
      (Q - controlledPrimeEll * (M / (8 * controlledPrimeEll)))) :
    n / d ≤ (y / d + 1) *
      (Q - controlledPrimeEll * (M / (8 * controlledPrimeEll))) := by
  let R := Q - controlledPrimeEll * (M / (8 * controlledPrimeEll))
  have hdiv : n / d ≤ (y * R) / d := Nat.div_le_div_right hroom
  apply hdiv.trans
  apply Nat.div_le_of_le_mul
  have hy : y < d * (y / d + 1) := by
    simpa [mul_comm] using Nat.lt_mul_div_succ y hd
  calc
    y * R ≤ (d * (y / d + 1)) * R :=
      Nat.mul_le_mul_right R hy.le
    _ = d * ((y / d + 1) * R) := by ring

/-- Seven scalar inequalities suffice for all eight post fields: diversity
is automatic, and the Lev ratio follows from the five-unit mass bound. -/
structure ControlledPrimeScalarPostRooms (n y : ℕ) : Prop where
  root_large : 12 * controlledPrimeEll ^ 2 ≤ fourthRootCeil y
  large_room : controlledPrimeL y + 2 * controlledPrimeU n ≤
    controlledPrimeExtractedFloorTwelve n y
  probability_small :
    (4 : ℝ) * (controlledPrimeClassCapTwelve n y + 1) * (2 * y + 1) *
      Real.exp (- ((controlledPrimeL y -
          (8 * controlledPrimeEll - 1) : ℕ) : ℝ) /
        (1024 * (controlledPrimeEll : ℝ) ^ 2)) < 1
  mass : 5 * controlledPrimeEll ^ 2 * controlledPrimeU n ≤
    y * controlledPrimeExtractedFloorTwelve n y
  width : 2 * y ≤ controlledPrimeEll *
    (y * controlledPrimeExtractedFloorTwelve n y /
      (controlledPrimeEll ^ 2 * controlledPrimeU n) - 1) + 1
  sum_room : 2 *
      (controlledPrimeEll *
        (controlledPrimeClassCapTwelve n y /
          (8 * controlledPrimeEll))) * y + controlledPrimeU n ≤ n
  unused_room : n ≤ y *
    (controlledPrimeExtractedFloorTwelve n y -
      controlledPrimeEll *
        (controlledPrimeClassCapTwelve n y /
          (8 * controlledPrimeEll)))

/-- The root threshold in the scalar room record is already a consequence
of the canonical endpoint estimates. -/
lemma eventually_controlledPrime_root_large :
    ∀ᶠ n : ℕ in atTop,
      12 * controlledPrimeEll ^ 2 ≤ fourthRootCeil
        (initialLowerY n (lowerColorCount 1 n)) := by
  let H : ℕ := 12 * controlledPrimeEll ^ 2
  have hpTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (1 / 8 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_controlledPrime_endpoint_parameters,
    hpTop.eventually (eventually_ge_atTop ((H ^ 4 : ℕ) : ℝ))] with
      n hend hp
  dsimp only at hend ⊢
  let y := initialLowerY n (lowerColorCount 1 n)
  have hUcast := (controlledPrimeU_cast_bounds n).1
  have hUlargeR : ((H ^ 4 : ℕ) : ℝ) ≤ controlledPrimeU n := by
    have hpnonneg : (0 : ℝ) ≤ Real.rpow (n : ℝ) (1 / 8 : ℝ) :=
      Real.rpow_nonneg (by positivity) _
    nlinarith
  have hUlarge : H ^ 4 ≤ controlledPrimeU n := by
    exact_mod_cast hUlargeR
  have hyLarge : H ^ 4 ≤ y := hUlarge.trans hend.2.1
  have hy : 0 < y := by omega
  by_contra hroot
  have hrootLt : fourthRootCeil y < H := Nat.lt_of_not_ge hroot
  have hyLt := fourthRootCeil_add_one_pow_four_gt hy
  have hpLe : (fourthRootCeil y + 1) ^ 4 ≤ H ^ 4 :=
    Nat.pow_le_pow_left (by omega) 4
  omega

/-- The seven scalar rooms produce the exact post record uniformly in the
extraction divisor and extracted cardinality. -/
theorem controlledPrimePostEstimates_of_scalarRooms
    {n y : ℕ} (hchoice : ControlledPrimeTwelveChoiceNumerics n y)
    (hroom : ControlledPrimeScalarPostRooms n y) :
    ControlledPrimePostEstimates n y := by
  have hn : 0 < n := by
    by_contra hn0
    have hnEq : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    have hUpos := hchoice.U_pos
    norm_num [controlledPrimeU] at hUpos
  have hres := controlledPrime_residual_large_of_root hroom.root_large
  refine ⟨hres, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d z hd _hdU _hQz _hzM
    exact controlledPrime_canonical_large_of_room hn hroom.large_room hd
  · intro d z hd _hdU _hQz _hzM
    exact controlledPrime_canonical_probability_ledger hd hres
      hroom.probability_small
  · intro d z _hd _hdU _hQz _hzM
    exact controlledPrime_canonical_diversity_ledger hres
  · intro d z hd hdU hQz _hzM
    exact (by omega : 3 ≤ 5).trans
      (controlledPrime_canonical_nzero_five_of_product
        hd hdU hQz hroom.mass)
  · intro d z hd hdU hQz _hzM
    exact controlledPrime_canonical_lev_of_five hd
      (controlledPrime_canonical_nzero_five_of_product
        hd hdU hQz hroom.mass)
  · intro d z hd hdU hQz _hzM
    have hden : 0 < controlledPrimeEll ^ 2 * d := by
      exact Nat.mul_pos (by norm_num [controlledPrimeEll]) hd
    have hmin :
        y * controlledPrimeExtractedFloorTwelve n y /
            (controlledPrimeEll ^ 2 * controlledPrimeU n) ≤
          primeRandomNzero y z controlledPrimeEll d := by
      unfold primeRandomNzero
      apply Nat.div_le_div
      · exact Nat.mul_le_mul_left y hQz
      · exact Nat.mul_le_mul_left (controlledPrimeEll ^ 2) hdU
      · exact hden.ne'
    exact hroom.width.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left controlledPrimeEll
        (Nat.sub_le_sub_right hmin 1)) 1)
  · intro d z hd hdU _hQz _hzM
    exact controlledPrime_canonical_sum_of_room hd hdU hroom.sum_room
  · intro d z hd _hdU _hQz _hzM
    exact controlledPrime_canonical_unused_of_room hd hroom.unused_room

/-- The elementary canonical choice bundle plus exactly the eight audited
post estimates constructs the truthful finite ledger. -/
theorem canonicalControlledPrimeNumericalLedger_of_post
    {n y : ℕ}
    (hchoice : ControlledPrimeTwelveChoiceNumerics n y)
    (hpost : ControlledPrimePostEstimates n y) :
    CFPControlledPrimeNumericalLedger n y
      (controlledPrimeU n) (controlledPrimeB n y) (controlledPrimeL y)
      (controlledPrimeClassCapTwelve n y)
      (controlledPrimeExtractedFloorTwelve n y) controlledPrimeEll := by
  refine ⟨by norm_num [controlledPrimeEll], hpost.residual_large,
    hchoice.U_pos, hchoice.B_pos, hchoice.B_cutoff,
    hchoice.U_pos.trans_le hchoice.U_le_floor, hchoice.loss_room, ?_⟩
  intro d z hd hdU hQz hzM
  exact ⟨hpost.large d z hd hdU hQz hzM,
    hpost.probability d z hd hdU hQz hzM,
    hpost.diversity d z hd hdU hQz hzM,
    hpost.nzero d z hd hdU hQz hzM,
    hpost.lev d z hd hdU hQz hzM,
    hpost.width d z hd hdU hQz hzM,
    hpost.sum d z hd hdU hQz hzM,
    hpost.unused d z hd hdU hQz hzM⟩

/-- Consequently, the only missing eventual numerical theorem is the
eventual validity of `ControlledPrimePostEstimates`; ordinary growth is not
part of this statement. -/
theorem eventually_canonicalControlledPrimeNumericalLedger_of_post
    (hpost : ∀ᶠ n : ℕ in atTop,
      ControlledPrimePostEstimates n
        (initialLowerY n (lowerColorCount 1 n))) :
    ∀ᶠ n : ℕ in atTop, CanonicalControlledPrimeNumericalLedger n := by
  filter_upwards [eventually_controlledPrimeTwelve_choice_numerics,
    hpost] with n hchoice hnpost
  exact canonicalControlledPrimeNumericalLedger_of_post hchoice hnpost

/-- Eventual scalar rooms are therefore sufficient for the complete
truthful numerical ledger. -/
theorem eventually_canonicalControlledPrimeNumericalLedger_of_scalarRooms
    (hroom : ∀ᶠ n : ℕ in atTop,
      ControlledPrimeScalarPostRooms n
        (initialLowerY n (lowerColorCount 1 n))) :
    ∀ᶠ n : ℕ in atTop, CanonicalControlledPrimeNumericalLedger n := by
  apply eventually_canonicalControlledPrimeNumericalLedger_of_post
  filter_upwards [eventually_controlledPrimeTwelve_choice_numerics,
    hroom] with n hchoice hnroom
  exact controlledPrimePostEstimates_of_scalarRooms hchoice hnroom

end Erdos360

#print axioms Erdos360.controlledRandomTestSetSource_of_numericalLedger
#print axioms Erdos360.canonicalControlledPrimeNumericalLedger_of_post
#print axioms Erdos360.controlledPrimePostEstimates_of_scalarRooms
