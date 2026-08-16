import Wikipedia.GreenTao.Sieve.CFZCarryBlockBoundary
import Wikipedia.GreenTao.Sieve.SelectedCFZAffineLocalProduct
import Wikipedia.SzemeredisTheorem.Finite.ProductMean

/-!
# Carry-block Euler products for selected CFZ families

The cyclic CFZ lift is not globally periodic modulo a paired divisor LCM:
crossing a representative boundary changes an integer carry.  The preceding
carry-block boundary file replaces that false periodicity by a sound
piecewise-affine model.  This file identifies the exact arithmetic model on
each complete quotient block.

For `D = pairedDivisorLcm z`, a complete block has the form

`x = r + D a`,  with `0 ≤ r_v < D`.

The carry is frozen at the lower corner `D a`.  Thus the block is governed
by the family

`q ↦ cfzCarryAdjustedAffineForm N W b q (cfzCarry q (D a))`.

Its mean over `r` is an exact squarefree CRT Euler product.  Averaging those
products over all complete blocks gives the global blockwise Euler model.
The only losses in comparing it with the original cyclic density are:

* the explicit carry-transition density from `CFZCarryBlockBoundary`;
* the outer partial-block boundary of size
  `O(D * card(CFZVariable k) / N)`.

The affine constants may depend arbitrarily on the block and on the form.
At primes dividing `W` they are still congruent to the reduced residue `b`,
so every supported local density is zero.  At good primes outside `W`,
one-form and rank-two geometry depends only on the coefficients, giving the
usual exact cardinality-at-most-two formula and the uniform `p⁻²` bound.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## A generic natural representative for an affine residue -/

/-- The standard natural representative of an integer affine form evaluated
on a residue vector. -/
def affineFormResidueValue
    {ι : Type*} [Fintype ι] {D : ℕ} [NeZero D]
    (ψ : AffineForm ι ℤ) (x : ι → ZMod D) : ℕ :=
  (ψ.evalZMod D x).val

@[simp]
theorem natCast_affineFormResidueValue
    {ι : Type*} [Fintype ι] {D : ℕ} [NeZero D]
    (ψ : AffineForm ι ℤ) (x : ι → ZMod D) :
    (affineFormResidueValue ψ x : ZMod D) =
      ψ.evalZMod D x :=
  ZMod.natCast_zmod_val _

/-- Natural representatives of arbitrary affine residues satisfy the prime
model required by the squarefree paired CRT theorem. -/
theorem pairedDivisibilityHasAffinePrimeModels_affineFormResidueValue
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (forms : κ → AffineForm ι ℤ)
    (z : κ → ℕ × ℕ) [NeZero (pairedDivisorLcm z)]
    (hz : SquarefreePairedDivisorChoice z) :
    PairedDivisibilityHasAffinePrimeModels z
      (fun q => affineFormResidueValue (forms q))
      forms hz := by
  intro x p q _hq
  have hpD :
      (p : ℕ) ∣ pairedDivisorLcm z :=
    Nat.dvd_of_mem_primeFactors p.2
  have hvalue :
      (affineFormResidueValue (forms q) x : ZMod (p : ℕ)) =
        (forms q).evalZMod (p : ℕ)
          (squarefreeCanonicalPrimeComponent hz p x) := by
    calc
      (affineFormResidueValue (forms q) x : ZMod (p : ℕ)) =
          ZMod.castHom hpD (ZMod (p : ℕ))
            (affineFormResidueValue (forms q) x :
              ZMod (pairedDivisorLcm z)) := by
            symm
            exact
              map_natCast
                (ZMod.castHom hpD (ZMod (p : ℕ)))
                (affineFormResidueValue (forms q) x)
      _ = ZMod.castHom hpD (ZMod (p : ℕ))
            ((forms q).evalZMod (pairedDivisorLcm z) x) := by
          rw [natCast_affineFormResidueValue]
      _ = (forms q).evalZMod (p : ℕ)
            (fun i =>
              ZMod.castHom hpD (ZMod (p : ℕ)) (x i)) :=
          castHom_affineForm_evalZMod hpD (forms q) x
      _ = (forms q).evalZMod (p : ℕ)
            (squarefreeCanonicalPrimeComponent hz p x) := by
          congr 1
          funext i
          exact
            (squarefreeCanonicalPrimeComponent_apply_eq_castHom
              hz p x i).symm
  rw [← ZMod.natCast_eq_zero_iff, hvalue]

/-- Exact squarefree CRT factorization for the natural representatives of
an arbitrary finite affine family. -/
theorem pairedDivisibilityDensity_affineFormResidueValue_eq_prod
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (forms : κ → AffineForm ι ℤ)
    (z : κ → ℕ × ℕ) [NeZero (pairedDivisorLcm z)]
    (hz : SquarefreePairedDivisorChoice z) :
    pairedDivisibilityDensity
        (fun q =>
          affineFormResidueValue
            (D := pairedDivisorLcm z) (forms q)) z =
      ∏ p : (pairedDivisorLcm z).primeFactors,
        affineFamilyZeroDensity (p : ℕ) forms
          (pairedPrimeSupport z p) := by
  exact
    pairedDivisibilityDensity_eq_prod_affineFamilyZeroDensity
      z
      (fun q =>
        affineFormResidueValue
          (D := pairedDivisorLcm z) (forms q))
      forms hz
      (pairedDivisibilityHasAffinePrimeModels_affineFormResidueValue
        forms z hz)

/-! ## Complete quotient blocks and their affine families -/

/-- The carry-adjusted affine family attached to the lower corner `D a` of
a quotient block. -/
def cfzCarryAdjustedFamilyAtBlock
    {κ : Type*} {k N : ℕ} [NeZero N]
    (D W b : ℕ) (forms : κ → CFZFormIndex k)
    (a : CFZVariable k → ℕ) (q : κ) :
    AffineForm (CFZVariable k) ℤ :=
  cfzCarryAdjustedAffineForm N W b (forms q)
    (cfzCarry (N := N) (forms q) (fun v => D * a v))

/-- The lower corner of `r + D a`, with `r` in the standard residue box,
is exactly `D a`. -/
theorem quotientBlockBase_residue_add_block
    {ι : Type*} {D : ℕ} (hD : 0 < D)
    (a : ι → ℕ) (r : FiniteBox (fun _ : ι => D)) :
    quotientBlockBase D
        (fun i => (r i : ℕ) + D * a i) =
      fun i => D * a i := by
  funext i
  simp only [quotientBlockBase]
  rw [Nat.add_mul_div_left _ _ hD, Nat.div_eq_of_lt (r i).isLt,
    Nat.zero_add]

/-- Adding the block offset does not change a coordinate modulo the block
side. -/
theorem natCast_residue_add_block
    {ι : Type*} {D : ℕ} [NeZero D]
    (a : ι → ℕ) (r : FiniteBox (fun _ : ι => D)) (i : ι) :
    ((r i : ℕ) + D * a i : ZMod D) =
      (r i : ℕ) := by
  simp

/-- On a complete block, the carry-block residue value is the ordinary
residue value of the fixed carry-adjusted affine form at that block. -/
theorem cfzCarryBlockAffineResidueValue_residue_add_block
    {κ : Type*} {k N D : ℕ} [NeZero N] [NeZero D]
    (hD : 0 < D) (W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (a : CFZVariable k → ℕ)
    (r : FiniteBox (fun _ : CFZVariable k => D))
    (q : κ) :
    cfzCarryBlockAffineResidueValue
        (N := N) (M := D) D W b (forms q)
        (fun v => (r v : ℕ) + D * a v) =
      affineFormResidueValue
        (D := D)
        (cfzCarryAdjustedFamilyAtBlock
          (N := N) D W b forms a q)
        (fun v => ((r v : ℕ) : ZMod D)) := by
  unfold cfzCarryBlockAffineResidueValue
    cfzCarryAdjustedFamilyAtBlock affineFormResidueValue
  rw [quotientBlockBase_residue_add_block hD a r]
  congr 2
  funext v
  change
    (((r v : ℕ) + D * a v : ℕ) : ZMod D) =
      ((r v : ℕ) : ZMod D)
  simp

/-! ## Good complete quotient blocks -/

/-- A complete quotient block is good for a finite CFZ family when its
lower corner is outside the family carry-bad set.  Because the bad set is a
union of whole quotient blocks, this is equivalent to carry constancy
throughout the complete block. -/
noncomputable def CFZFamilyGoodQuotientBlock
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (D : ℕ) (forms : κ → CFZFormIndex k)
    (a : FiniteBox (fun _ : CFZVariable k => N / D)) : Prop :=
  (fun v => D * (a v : ℕ)) ∉
    cfzFamilyCarryBadPoints (N := N) D forms

/-- The lower corner of a complete positive-side quotient block lies in
the original `N`-box. -/
theorem completeQuotientBlockLowerCorner_mem_natBox
    {k N D : ℕ} (hD : 0 < D)
    (a : FiniteBox (fun _ : CFZVariable k => N / D)) :
    (fun v => D * (a v : ℕ)) ∈
      natBox (fun _ : CFZVariable k => N) := by
  rw [mem_natBox]
  intro v
  calc
    D * (a v : ℕ) = (a v : ℕ) * D :=
      Nat.mul_comm _ _
    _ < (N / D) * D :=
      Nat.mul_lt_mul_of_pos_right (a v).isLt hD
    _ ≤ N :=
      Nat.div_mul_le_self N D

/-- On a good complete quotient block every selected carry equals the carry
sampled at its lower corner. -/
theorem cfzCarry_eq_lowerCorner_of_goodQuotientBlock
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N]
    (hD : 0 < D) (forms : κ → CFZFormIndex k)
    (a : FiniteBox (fun _ : CFZVariable k => N / D))
    (hgood : CFZFamilyGoodQuotientBlock
      (N := N) D forms a)
    (q : κ) {x : CFZVariable k → ℕ}
    (hx : x ∈ natBox (fun _ : CFZVariable k => N))
    (hblock :
      SameQuotientBlock D
        (fun v => D * (a v : ℕ)) x) :
    cfzCarry (N := N) (forms q) x =
      cfzCarry (N := N) (forms q)
        (fun v => D * (a v : ℕ)) := by
  by_contra hne
  apply hgood
  apply Finset.mem_biUnion.mpr
  refine ⟨q, Finset.mem_univ q,
    mem_cfzCarryBadPoints.mpr ?_⟩
  refine
    ⟨completeQuotientBlockLowerCorner_mem_natBox hD a,
      x, hx, hblock, ?_⟩
  exact fun h => hne h.symm

/-- Every good complete quotient block is a simultaneous carry cell with
the advertised carry-dependent constants. -/
theorem isCFZCarryCell_completeQuotientBlock_of_good
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N]
    (hD : 0 < D) (forms : κ → CFZFormIndex k)
    (a : FiniteBox (fun _ : CFZVariable k => N / D))
    (hgood : CFZFamilyGoodQuotientBlock
      (N := N) D forms a) :
    IsCFZCarryCell (N := N) forms
      (fun q =>
        cfzCarry (N := N) (forms q)
          (fun v => D * (a v : ℕ)))
      (quotientBlock N D
        (fun v => D * (a v : ℕ))) := by
  exact
    isCFZCarryCell_quotientBlock_of_not_mem_bad
      forms (fun v => D * (a v : ℕ))
      (completeQuotientBlockLowerCorner_mem_natBox hD a)
      hgood

/-- Every residue point `r + D a` of a good complete quotient block is
outside the family carry-bad set. -/
theorem residue_add_block_not_mem_bad_of_goodQuotientBlock
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N]
    (hD : 0 < D) (forms : κ → CFZFormIndex k)
    (a : FiniteBox (fun _ : CFZVariable k => N / D))
    (hgood : CFZFamilyGoodQuotientBlock
      (N := N) D forms a)
    (r : FiniteBox (fun _ : CFZVariable k => D)) :
    (fun v => (r v : ℕ) + D * (a v : ℕ)) ∉
      cfzFamilyCarryBadPoints (N := N) D forms := by
  let x : CFZVariable k → ℕ :=
    fun v => (r v : ℕ) + D * (a v : ℕ)
  have hx : x ∈ natBox (fun _ : CFZVariable k => N) := by
    rw [mem_natBox]
    intro v
    calc
      (r v : ℕ) + D * (a v : ℕ) <
          D + D * (a v : ℕ) :=
        Nat.add_lt_add_right (r v).isLt _
      _ = D * ((a v : ℕ) + 1) := by ring
      _ ≤ D * (N / D) := by
        gcongr
        exact (a v).isLt
      _ = (N / D) * D := by ring
      _ ≤ N := Nat.div_mul_le_self N D
  have hbase :
      quotientBlockBase D x =
        fun v => D * (a v : ℕ) := by
    exact quotientBlockBase_residue_add_block
      hD (fun v => (a v : ℕ)) r
  have hsame :
      SameQuotientBlock D
        (fun v => D * (a v : ℕ)) x := by
    rw [← hbase]
    exact
      (sameQuotientBlock_quotientBlockBase hD x).symm
  intro hbad
  obtain ⟨q, _hq, hqbad⟩ :=
    Finset.mem_biUnion.mp hbad
  obtain ⟨_hx, y, hy, hxy, hcarry⟩ :=
    mem_cfzCarryBadPoints.mp hqbad
  have hxcarry :=
    cfzCarry_eq_lowerCorner_of_goodQuotientBlock
      hD forms a hgood q hx hsame
  have hycarry :=
    cfzCarry_eq_lowerCorner_of_goodQuotientBlock
      hD forms a hgood q hy (hsame.trans hxy)
  exact hcarry (hxcarry.trans hycarry.symm)

/-- Pointwise equality between the original cyclic paired indicator and the
fixed affine residue model on every good complete quotient block. -/
theorem pairedDivisibilityIndicator_cfz_eq_affineResidue_on_goodQuotientBlock
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (a : FiniteBox (fun _ : CFZVariable k =>
      N / pairedDivisorLcm z))
    (hgood : CFZFamilyGoodQuotientBlock
      (N := N) (pairedDivisorLcm z) forms a)
    (r : FiniteBox (fun _ : CFZVariable k =>
      pairedDivisorLcm z)) :
    pairedDivisibilityIndicator
        (fun q y =>
          cfzWTrickedLinearValue W b (forms q)
            (cubePointOfNat (N := N) y))
        z
        (fun v =>
          (r v : ℕ) + pairedDivisorLcm z * (a v : ℕ)) =
      pairedDivisibilityIndicator
        (fun q =>
          affineFormResidueValue
            (D := pairedDivisorLcm z)
            (cfzCarryAdjustedFamilyAtBlock
              (N := N) (pairedDivisorLcm z) W b forms
              (fun v => (a v : ℕ)) q))
        z
        (fun v =>
          ((r v : ℕ) : ZMod (pairedDivisorLcm z))) := by
  have hD : 0 < pairedDivisorLcm z :=
    NeZero.pos _
  have hvalue :=
    pairedDivisibilityIndicator_cfz_eq_carryBlockAffineResidue_of_not_bad
      (N := N) hD W b forms z
      (x := fun v =>
        (r v : ℕ) + pairedDivisorLcm z * (a v : ℕ))
      (by
        rw [mem_natBox]
        intro v
        calc
          (r v : ℕ) +
                pairedDivisorLcm z * (a v : ℕ) <
              pairedDivisorLcm z +
                pairedDivisorLcm z * (a v : ℕ) :=
            Nat.add_lt_add_right (r v).isLt _
          _ = pairedDivisorLcm z *
              ((a v : ℕ) + 1) := by ring
          _ ≤ pairedDivisorLcm z *
              (N / pairedDivisorLcm z) := by
            gcongr
            exact (a v).isLt
          _ = (N / pairedDivisorLcm z) *
              pairedDivisorLcm z := by ring
          _ ≤ N :=
            Nat.div_mul_le_self N (pairedDivisorLcm z))
      (residue_add_block_not_mem_bad_of_goodQuotientBlock
        hD forms a hgood r)
  rw [hvalue]
  unfold pairedDivisibilityIndicator
  apply Finset.prod_congr rfl
  intro q _hq
  change
    natDivisibilityIndicator (z q).1
        (cfzCarryBlockAffineResidueValue
          (N := N) (M := pairedDivisorLcm z)
          (pairedDivisorLcm z) W b (forms q)
          (fun v =>
            (r v : ℕ) +
              pairedDivisorLcm z * (a v : ℕ))) *
      natDivisibilityIndicator (z q).2
        (cfzCarryBlockAffineResidueValue
          (N := N) (M := pairedDivisorLcm z)
          (pairedDivisorLcm z) W b (forms q)
          (fun v =>
            (r v : ℕ) +
              pairedDivisorLcm z * (a v : ℕ))) =
      natDivisibilityIndicator (z q).1
        (affineFormResidueValue
          (D := pairedDivisorLcm z)
          (cfzCarryAdjustedFamilyAtBlock
            (N := N) (pairedDivisorLcm z) W b forms
            (fun v => (a v : ℕ)) q)
          (fun v =>
            ((r v : ℕ) : ZMod (pairedDivisorLcm z)))) *
      natDivisibilityIndicator (z q).2
        (affineFormResidueValue
          (D := pairedDivisorLcm z)
          (cfzCarryAdjustedFamilyAtBlock
            (N := N) (pairedDivisorLcm z) W b forms
            (fun v => (a v : ℕ)) q)
          (fun v =>
            ((r v : ℕ) : ZMod (pairedDivisorLcm z))))
  rw [cfzCarryBlockAffineResidueValue_residue_add_block
    hD W b forms (fun v => (a v : ℕ)) r q]

/-! ## Exact blockwise CRT and averaged Euler products -/

/-- Every complete carry block has an exact squarefree Euler product. -/
theorem pairedDivisibilityDensity_cfzCarryBlock_eq_eulerProduct
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ) (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ) [NeZero (pairedDivisorLcm z)]
    (hz : SquarefreePairedDivisorChoice z)
    (a : CFZVariable k → ℕ) :
    pairedDivisibilityDensity
        (fun q =>
          affineFormResidueValue
            (D := pairedDivisorLcm z)
            (cfzCarryAdjustedFamilyAtBlock
              (N := N) (pairedDivisorLcm z) W b forms a q))
        z =
      ∏ p : (pairedDivisorLcm z).primeFactors,
        affineFamilyZeroDensity (p : ℕ)
          (cfzCarryAdjustedFamilyAtBlock
            (N := N) (pairedDivisorLcm z) W b forms a)
          (pairedPrimeSupport z p) := by
  exact
    pairedDivisibilityDensity_affineFormResidueValue_eq_prod
      (cfzCarryAdjustedFamilyAtBlock
        (N := N) (pairedDivisorLcm z) W b forms a)
      z hz

/-- Mean over all complete quotient blocks of their exact local-factor
products.  The quotient side `N / D` deliberately omits the final partial
block in each coordinate. -/
noncomputable def cfzCarryBlockEulerAverage
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ) (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ) : ℝ :=
  mean (fun a :
      FiniteBox (fun _ : CFZVariable k =>
        N / pairedDivisorLcm z) =>
    ∏ p : (pairedDivisorLcm z).primeFactors,
      affineFamilyZeroDensity (p : ℕ)
        (cfzCarryAdjustedFamilyAtBlock
          (N := N) (pairedDivisorLcm z) W b forms
          (fun v => (a v : ℕ)))
        (pairedPrimeSupport z p))

/-- A box whose side is `q_v D` is the iterated mean over quotient blocks
and residues.  No periodicity is assumed. -/
theorem boxMean_mul_eq_mean₂_quotient_residue
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℕ) (D : ℕ) (F : (ι → ℕ) → ℝ) :
    boxMean (fun i => q i * D) F =
      mean₂ (fun a : FiniteBox q =>
        fun r : FiniteBox (fun _ : ι => D) =>
          F (fun i => (r i : ℕ) + D * (a i : ℕ))) := by
  rw [boxMean_eq_mean_finiteBox]
  calc
    mean (fun x : FiniteBox (fun i => q i * D) =>
        F (fun i => (x i : ℕ))) =
        mean (fun x :
            FiniteBox q × FiniteBox (fun _ : ι => D) =>
          F (fun i =>
            ((boxQuotientEquiv q D x) i : ℕ))) := by
      unfold mean
      apply Fintype.expect_equiv (boxQuotientEquiv q D).symm
      intro x
      congr 1
      funext i
      simp
    _ = mean₂ (fun a : FiniteBox q =>
        fun r : FiniteBox (fun _ : ι => D) =>
          F (fun i => (r i : ℕ) + D * (a i : ℕ))) := by
      simpa only [boxQuotientEquiv_apply_val] using
        mean_prod_type
          (fun a : FiniteBox q =>
            fun r : FiniteBox (fun _ : ι => D) =>
              F (fun i => (r i : ℕ) + D * (a i : ℕ)))

/-! ## The complete-block mean is the averaged Euler product -/

/-- The carry-block residue model restricted to the union of complete
`D`-blocks is exactly the average of the blockwise Euler products. -/
theorem boxMean_cfzCarryBlockResidue_trimmed_eq_eulerAverage
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ) (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ) [NeZero (pairedDivisorLcm z)]
    (hz : SquarefreePairedDivisorChoice z) :
    boxMean
        (fun _ : CFZVariable k =>
          trimToMultiple (pairedDivisorLcm z) N)
        (pairedDivisibilityIndicator
          (fun q x =>
            cfzCarryBlockAffineResidueValue
              (N := N) (M := pairedDivisorLcm z)
              (pairedDivisorLcm z) W b (forms q) x)
          z) =
      cfzCarryBlockEulerAverage
        (N := N) W b forms z := by
  let D := pairedDivisorLcm z
  have hD : 0 < D := by
    dsimp only [D]
    exact NeZero.pos _
  have hdecomp :=
    boxMean_mul_eq_mean₂_quotient_residue
      (fun _ : CFZVariable k => N / D) D
      (pairedDivisibilityIndicator
        (fun q x =>
          cfzCarryBlockAffineResidueValue
            (N := N) (M := D) D W b (forms q) x)
        z)
  change
    boxMean
        (fun _ : CFZVariable k => N / D * D)
        (pairedDivisibilityIndicator
          (fun q x =>
            cfzCarryBlockAffineResidueValue
              (N := N) (M := D) D W b (forms q) x)
          z) =
      _
  rw [hdecomp]
  unfold cfzCarryBlockEulerAverage mean₂
  apply congrArg mean
  funext a
  have hresidue :
      mean (fun r : FiniteBox (fun _ : CFZVariable k => D) =>
          pairedDivisibilityIndicator
            (fun q x =>
              cfzCarryBlockAffineResidueValue
                (N := N) (M := D) D W b (forms q) x)
            z
            (fun i => (r i : ℕ) + D * (a i : ℕ))) =
        pairedDivisibilityDensity
          (fun q =>
            affineFormResidueValue
              (D := D)
              (cfzCarryAdjustedFamilyAtBlock
                (N := N) D W b forms
                (fun v => (a v : ℕ)) q))
          z := by
    unfold pairedDivisibilityDensity mean
    apply Fintype.expect_equiv (finiteBoxEquivZModVector D)
    intro r
    unfold pairedDivisibilityIndicator
    apply Finset.prod_congr rfl
    intro q _hq
    change
      natDivisibilityIndicator (z q).1
          (cfzCarryBlockAffineResidueValue
            (N := N) (M := D) D W b (forms q)
            (fun i => (r i : ℕ) + D * (a i : ℕ))) *
        natDivisibilityIndicator (z q).2
          (cfzCarryBlockAffineResidueValue
            (N := N) (M := D) D W b (forms q)
            (fun i => (r i : ℕ) + D * (a i : ℕ))) =
        natDivisibilityIndicator (z q).1
          (affineFormResidueValue
            (D := D)
            (cfzCarryAdjustedFamilyAtBlock
              (N := N) D W b forms
              (fun v => (a v : ℕ)) q)
            (fun v => ((r v : ℕ) : ZMod D))) *
        natDivisibilityIndicator (z q).2
          (affineFormResidueValue
            (D := D)
            (cfzCarryAdjustedFamilyAtBlock
              (N := N) D W b forms
              (fun v => (a v : ℕ)) q)
            (fun v => ((r v : ℕ) : ZMod D)))
    rw [cfzCarryBlockAffineResidueValue_residue_add_block
      hD W b forms (fun v => (a v : ℕ)) r q]
  rw [hresidue]
  exact
    pairedDivisibilityDensity_cfzCarryBlock_eq_eulerProduct
      W b forms z hz (fun v => (a v : ℕ))

/-! ## The outer partial-block boundary -/

/-- Trimming a bounded box function to complete coordinatewise blocks costs
at most twice the relative number of removed points.  This statement needs
no periodicity. -/
theorem abs_boxMean_sub_trimmedBoxMean_le_boundary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ℕ) (side : ι → ℕ)
    (F : (ι → ℕ) → ℝ) (B : ℝ)
    (hD : 0 < D) (hside : ∀ i, D ≤ side i)
    (hbound : ∀ x, |F x| ≤ B) :
    |boxMean side F - boxMean (trimmedSide D side) F| ≤
      2 *
        (((∏ i, side i) -
          ∏ i, trimToMultiple D (side i) : ℕ) : ℝ) *
        B /
        ∏ i, (side i : ℝ) := by
  have hsidepos : ∀ i, 0 < side i :=
    fun i => hD.trans_le (hside i)
  have htrimpos : ∀ i, 0 < trimmedSide D side i := by
    intro i
    change 0 < side i / D * D
    exact Nat.mul_pos (Nat.div_pos (hside i) hD) hD
  have hprodle :
      (∏ i, trimmedSide D side i) ≤ ∏ i, side i := by
    apply Finset.prod_le_prod
    · intro i _hi
      exact Nat.zero_le _
    · intro i _hi
      exact trimmedSide_le D side i
  have hvolume :
      (∏ i, (side i : ℝ)) -
          ∏ i, (trimmedSide D side i : ℝ) =
        (((∏ i, side i) -
          ∏ i, trimmedSide D side i : ℕ) : ℝ) := by
    rw [← Nat.cast_prod, ← Nat.cast_prod, Nat.cast_sub hprodle]
  have hsum :
      |boxSum side F - boxSum (trimmedSide D side) F| ≤
        (((∏ i, side i) -
          ∏ i, trimmedSide D side i : ℕ) : ℝ) * B :=
    abs_boxSum_sub_trimmed_le_explicit D side F B
      (fun x _hx => hbound x)
  have hV : 0 < ∏ i, (side i : ℝ) := by
    apply Finset.prod_pos
    intro i _hi
    exact_mod_cast hsidepos i
  have hU : 0 < ∏ i, (trimmedSide D side i : ℝ) := by
    apply Finset.prod_pos
    intro i _hi
    exact_mod_cast htrimpos i
  have hE :
      0 ≤ (((∏ i, side i) -
        ∏ i, trimmedSide D side i : ℕ) : ℝ) := by
    positivity
  have htrimmean :
      |boxSum (trimmedSide D side) F /
          ∏ i, (trimmedSide D side i : ℝ)| ≤ B := by
    rw [← boxMean]
    rw [boxMean_eq_mean_finiteBox]
    let x₀ : FiniteBox (trimmedSide D side) :=
      fun i => ⟨0, htrimpos i⟩
    letI : Nonempty (FiniteBox (trimmedSide D side)) := ⟨x₀⟩
    apply abs_le.mpr
    constructor
    · exact
        const_le_mean
          (fun x =>
            neg_le_of_abs_le
              (hbound (fun i => (x i : ℕ))))
    · exact
        mean_le_of_le_const
          (fun x =>
            le_of_abs_le
              (hbound (fun i => (x i : ℕ))))
  have hnormalize :=
    abs_div_sub_div_le_two_mul_boundary
      hV hU hE hvolume hsum htrimmean
  change
    |boxMean side F - boxMean (trimmedSide D side) F| ≤
      2 *
        (((∏ i, side i) -
          ∏ i, trimmedSide D side i : ℕ) : ℝ) *
        B /
        ∏ i, (side i : ℝ) at hnormalize
  simpa [trimmedSide] using hnormalize

/-- The full carry-block residue model differs from the averaged Euler
product only by the outer incomplete blocks. -/
theorem
    abs_cfzCarryBlockPairedResidueModelDensity_sub_eulerAverage_le_boundary
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ) (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ) [NeZero (pairedDivisorLcm z)]
    (hz : SquarefreePairedDivisorChoice z)
    (hDN : pairedDivisorLcm z ≤ N) :
    |cfzCarryBlockPairedResidueModelDensity
        (N := N) (pairedDivisorLcm z) W b forms z -
      cfzCarryBlockEulerAverage
        (N := N) W b forms z| ≤
      2 *
        (((N ^ Fintype.card (CFZVariable k) -
          (trimToMultiple (pairedDivisorLcm z) N) ^
            Fintype.card (CFZVariable k) : ℕ) : ℝ)) /
        (N : ℝ) ^ Fintype.card (CFZVariable k) := by
  let D := pairedDivisorLcm z
  let F : (CFZVariable k → ℕ) → ℝ :=
    pairedDivisibilityIndicator
      (fun q x =>
        cfzCarryBlockAffineResidueValue
          (N := N) (M := D) D W b (forms q) x)
      z
  have hD : 0 < D := by
    dsimp only [D]
    exact NeZero.pos _
  have hbound : ∀ x, |F x| ≤ (1 : ℝ) :=
    fun x =>
      abs_pairedDivisibilityIndicator_le_one
        (fun q y =>
          cfzCarryBlockAffineResidueValue
            (N := N) (M := D) D W b (forms q) y)
        z x
  have hboundary :=
    abs_boxMean_sub_trimmedBoxMean_le_boundary
      D (fun _ : CFZVariable k => N) F 1
      hD (fun _ => hDN) hbound
  have htrim :
      boxMean
          (trimmedSide D
            (fun _ : CFZVariable k => N)) F =
        cfzCarryBlockEulerAverage
          (N := N) W b forms z := by
    change
      boxMean
          (fun _ : CFZVariable k =>
            trimToMultiple D N) F =
        cfzCarryBlockEulerAverage
          (N := N) W b forms z
    simpa [D, F] using
      boxMean_cfzCarryBlockResidue_trimmed_eq_eulerAverage
        W b forms z hz
  rw [htrim] at hboundary
  change
    |cfzCarryBlockPairedResidueModelDensity
        (N := N) D W b forms z -
      cfzCarryBlockEulerAverage
        (N := N) W b forms z| ≤ _
  simpa [cfzCarryBlockPairedResidueModelDensity, D, F,
    Finset.prod_const, Finset.card_univ] using hboundary

/-- Power-form version of the outer partial-block loss. -/
theorem
    abs_cfzCarryBlockPairedResidueModelDensity_sub_eulerAverage_le_linear
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ) (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ) [NeZero (pairedDivisorLcm z)]
    (hz : SquarefreePairedDivisorChoice z)
    (hDN : pairedDivisorLcm z ≤ N) :
    |cfzCarryBlockPairedResidueModelDensity
        (N := N) (pairedDivisorLcm z) W b forms z -
      cfzCarryBlockEulerAverage
        (N := N) W b forms z| ≤
      2 * (pairedDivisorLcm z : ℝ) *
        (Fintype.card (CFZVariable k) : ℝ) *
        (N : ℝ) ^ (Fintype.card (CFZVariable k) - 1) /
        (N : ℝ) ^ Fintype.card (CFZVariable k) := by
  have hbase :=
    abs_cfzCarryBlockPairedResidueModelDensity_sub_eulerAverage_le_boundary
      W b forms z hz hDN
  have hD : 0 < pairedDivisorLcm z :=
    NeZero.pos _
  have hboundary :=
    cast_pow_sub_trimToMultiple_pow_le
      hD (N := N) (t := Fintype.card (CFZVariable k))
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast NeZero.pos N
  calc
    |cfzCarryBlockPairedResidueModelDensity
        (N := N) (pairedDivisorLcm z) W b forms z -
      cfzCarryBlockEulerAverage
        (N := N) W b forms z| ≤
        2 *
          (((N ^ Fintype.card (CFZVariable k) -
            (trimToMultiple (pairedDivisorLcm z) N) ^
              Fintype.card (CFZVariable k) : ℕ) : ℝ)) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) :=
      hbase
    _ ≤
        2 * (pairedDivisorLcm z : ℝ) *
          (Fintype.card (CFZVariable k) : ℝ) *
          (N : ℝ) ^ (Fintype.card (CFZVariable k) - 1) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt (pow_pos hNpos _))
      have htwo : (0 : ℝ) ≤ 2 := by norm_num
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hboundary htwo

/-! ## Unconditional cyclic-to-Euler approximation -/

/-- The sharp bookkeeping form of the blockwise Euler approximation.  The
first summand is precisely the carry-bad density; the second is precisely
the outer partial-block boundary. -/
theorem
    abs_pairedDivisibilityDensity_cfz_sub_carryBlockEulerAverage_le_bad_add_boundary
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ) (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ) [NeZero (pairedDivisorLcm z)]
    (hz : SquarefreePairedDivisorChoice z)
    (hDN : pairedDivisorLcm z ≤ N) :
    |pairedDivisibilityDensity
        (fun q (x : CubePoint k N) =>
          cfzWTrickedLinearValue W b (forms q) x)
        z -
      cfzCarryBlockEulerAverage
        (N := N) W b forms z| ≤
      ((cfzFamilyCarryBadPoints
        (N := N) (pairedDivisorLcm z) forms).card : ℝ) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) +
        2 *
          (((N ^ Fintype.card (CFZVariable k) -
            (trimToMultiple (pairedDivisorLcm z) N) ^
              Fintype.card (CFZVariable k) : ℕ) : ℝ)) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) := by
  let actual :=
    pairedDivisibilityDensity
      (fun q (x : CubePoint k N) =>
        cfzWTrickedLinearValue W b (forms q) x)
      z
  let block :=
    cfzCarryBlockPairedResidueModelDensity
      (N := N) (pairedDivisorLcm z) W b forms z
  let euler :=
    cfzCarryBlockEulerAverage
      (N := N) W b forms z
  have hD : 0 < pairedDivisorLcm z :=
    NeZero.pos _
  have hcarry :
      |actual - block| ≤
        ((cfzFamilyCarryBadPoints
          (N := N) (pairedDivisorLcm z) forms).card : ℝ) /
            (N : ℝ) ^ Fintype.card (CFZVariable k) := by
    simpa only [actual, block] using
      abs_pairedDivisibilityDensity_cfz_sub_carryBlockResidueModel_le_bad
        (N := N) hD W b forms z
  have houter :
      |block - euler| ≤
        2 *
          (((N ^ Fintype.card (CFZVariable k) -
            (trimToMultiple (pairedDivisorLcm z) N) ^
              Fintype.card (CFZVariable k) : ℕ) : ℝ)) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) := by
    simpa only [block, euler] using
      abs_cfzCarryBlockPairedResidueModelDensity_sub_eulerAverage_le_boundary
        W b forms z hz hDN
  change |actual - euler| ≤ _
  calc
    |actual - euler| =
        |(actual - block) + (block - euler)| := by
      congr 1
      ring
    _ ≤ |actual - block| + |block - euler| :=
      abs_add_le _ _
    _ ≤
        ((cfzFamilyCarryBadPoints
          (N := N) (pairedDivisorLcm z) forms).card : ℝ) /
            (N : ℝ) ^ Fintype.card (CFZVariable k) +
          2 *
            (((N ^ Fintype.card (CFZVariable k) -
              (trimToMultiple (pairedDivisorLcm z) N) ^
                Fintype.card (CFZVariable k) : ℕ) : ℝ)) /
            (N : ℝ) ^ Fintype.card (CFZVariable k) :=
      add_le_add hcarry houter

/-- Explicit `O_{k,|κ|}(D/N)` cyclic-to-Euler estimate, with the carry
transition loss and outer partial-block loss displayed separately. -/
theorem
    abs_pairedDivisibilityDensity_cfz_sub_carryBlockEulerAverage_le_linear
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (hk : 2 ≤ k)
    (W b : ℕ) (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ) [NeZero (pairedDivisorLcm z)]
    (hz : SquarefreePairedDivisorChoice z)
    (hDN : pairedDivisorLcm z ≤ N) :
    |pairedDivisibilityDensity
        (fun q (x : CubePoint k N) =>
          cfzWTrickedLinearValue W b (forms q) x)
        z -
      cfzCarryBlockEulerAverage
        (N := N) W b forms z| ≤
      (Fintype.card κ : ℝ) *
          (2 * cfzCarryRange k + 1) *
          (2 * Fintype.card (CFZVariable k) * k + 1) *
          (pairedDivisorLcm z : ℝ) *
          (N : ℝ) ^
            (Fintype.card (CFZVariable k) - 1) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) +
        2 * (pairedDivisorLcm z : ℝ) *
          (Fintype.card (CFZVariable k) : ℝ) *
          (N : ℝ) ^
            (Fintype.card (CFZVariable k) - 1) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) := by
  let actual :=
    pairedDivisibilityDensity
      (fun q (x : CubePoint k N) =>
        cfzWTrickedLinearValue W b (forms q) x)
      z
  let block :=
    cfzCarryBlockPairedResidueModelDensity
      (N := N) (pairedDivisorLcm z) W b forms z
  let euler :=
    cfzCarryBlockEulerAverage
      (N := N) W b forms z
  have hD : 0 < pairedDivisorLcm z :=
    NeZero.pos _
  have hcarry :
      |actual - block| ≤
        (Fintype.card κ : ℝ) *
          (2 * cfzCarryRange k + 1) *
          (2 * Fintype.card (CFZVariable k) * k + 1) *
          (pairedDivisorLcm z : ℝ) *
          (N : ℝ) ^
            (Fintype.card (CFZVariable k) - 1) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) := by
    simpa only [actual, block] using
      abs_pairedDivisibilityDensity_cfz_sub_carryBlockResidueModel_le_linear
        (N := N) hk hD W b forms z
  have houter :
      |block - euler| ≤
        2 * (pairedDivisorLcm z : ℝ) *
          (Fintype.card (CFZVariable k) : ℝ) *
          (N : ℝ) ^
            (Fintype.card (CFZVariable k) - 1) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) := by
    simpa only [block, euler] using
      abs_cfzCarryBlockPairedResidueModelDensity_sub_eulerAverage_le_linear
        W b forms z hz hDN
  change |actual - euler| ≤ _
  calc
    |actual - euler| =
        |(actual - block) + (block - euler)| := by
      congr 1
      ring
    _ ≤ |actual - block| + |block - euler| :=
      abs_add_le _ _
    _ ≤ _ :=
      add_le_add hcarry houter

/-- A single explicit coefficient for the two `O(D/N)` losses: carry
transitions for `familyCard` forms and the outer partial blocks. -/
def cfzCarryBlockEulerErrorConstant
    (k familyCard : ℕ) : ℕ :=
  familyCard *
      (2 * cfzCarryRange k + 1) *
      (2 * Fintype.card (CFZVariable k) * k + 1) +
    2 * Fintype.card (CFZVariable k)

/-- Collapsed `C_{k,|κ|} D/N` form of the blockwise Euler approximation. -/
theorem
    abs_pairedDivisibilityDensity_cfz_sub_carryBlockEulerAverage_le_div
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (hk : 2 ≤ k)
    (W b : ℕ) (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ) [NeZero (pairedDivisorLcm z)]
    (hz : SquarefreePairedDivisorChoice z)
    (hDN : pairedDivisorLcm z ≤ N) :
    |pairedDivisibilityDensity
        (fun q (x : CubePoint k N) =>
          cfzWTrickedLinearValue W b (forms q) x)
        z -
      cfzCarryBlockEulerAverage
        (N := N) W b forms z| ≤
      (cfzCarryBlockEulerErrorConstant
          k (Fintype.card κ) : ℝ) *
        (pairedDivisorLcm z : ℝ) / (N : ℝ) := by
  have hbase :=
    abs_pairedDivisibilityDensity_cfz_sub_carryBlockEulerAverage_le_linear
      hk W b forms z hz hDN
  let t := Fintype.card (CFZVariable k)
  have hkpos : 0 < k := by omega
  have htpos : 0 < t := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨(⟨0, hkpos⟩, false)⟩
  have htOne : 1 ≤ t := htpos
  have hpow :
      (N : ℝ) ^ t =
        (N : ℝ) ^ (t - 1) * (N : ℝ) := by
    calc
      (N : ℝ) ^ t =
          (N : ℝ) ^ ((t - 1) + 1) := by
        rw [Nat.sub_add_cancel htOne]
      _ = (N : ℝ) ^ (t - 1) * (N : ℝ) := by
        rw [pow_succ]
  have hNne : (N : ℝ) ≠ 0 := by
    exact_mod_cast NeZero.ne N
  calc
    |pairedDivisibilityDensity
        (fun q (x : CubePoint k N) =>
          cfzWTrickedLinearValue W b (forms q) x)
        z -
      cfzCarryBlockEulerAverage
        (N := N) W b forms z| ≤
      (Fintype.card κ : ℝ) *
          (2 * cfzCarryRange k + 1) *
          (2 * Fintype.card (CFZVariable k) * k + 1) *
          (pairedDivisorLcm z : ℝ) *
          (N : ℝ) ^
            (Fintype.card (CFZVariable k) - 1) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) +
        2 * (pairedDivisorLcm z : ℝ) *
          (Fintype.card (CFZVariable k) : ℝ) *
          (N : ℝ) ^
            (Fintype.card (CFZVariable k) - 1) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) :=
      hbase
    _ =
      (cfzCarryBlockEulerErrorConstant
          k (Fintype.card κ) : ℝ) *
        (pairedDivisorLcm z : ℝ) / (N : ℝ) := by
      change
        (Fintype.card κ : ℝ) *
              (2 * cfzCarryRange k + 1) *
              (2 * t * k + 1) *
              (pairedDivisorLcm z : ℝ) *
              (N : ℝ) ^ (t - 1) /
              (N : ℝ) ^ t +
            2 * (pairedDivisorLcm z : ℝ) *
              (t : ℝ) * (N : ℝ) ^ (t - 1) /
              (N : ℝ) ^ t =
          (cfzCarryBlockEulerErrorConstant
              k (Fintype.card κ) : ℝ) *
            (pairedDivisorLcm z : ℝ) / (N : ℝ)
      rw [hpow]
      unfold cfzCarryBlockEulerErrorConstant
      push_cast
      field_simp
      ring

/-! ## Selected-family specialization -/

/-- The averaged block Euler product for the selected CFZ subfamily encoded
by `e`. -/
noncomputable def selectedCFZCarryBlockEulerAverage
    {k N : ℕ} [NeZero N]
    (e : LinearFormsExponent k)
    (W b : ℕ)
    (z : SelectedCFZFormIndex e → ℕ × ℕ) : ℝ :=
  cfzCarryBlockEulerAverage
    (N := N) W b
    (fun q : SelectedCFZFormIndex e => q.1) z

/-- Exact carry-bad plus outer-boundary estimate for an arbitrary selected
CFZ subfamily. -/
theorem
    abs_pairedDivisibilityDensity_selectedCFZ_sub_carryBlockEulerAverage_le_bad_add_boundary
    {k N : ℕ} [NeZero N]
    (e : LinearFormsExponent k)
    (W b : ℕ)
    (z : SelectedCFZFormIndex e → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (hz : SquarefreePairedDivisorChoice z)
    (hDN : pairedDivisorLcm z ≤ N) :
    |pairedDivisibilityDensity
        (fun q : SelectedCFZFormIndex e =>
          fun x : CubePoint k N =>
            cfzWTrickedLinearValue W b q.1 x)
        z -
      selectedCFZCarryBlockEulerAverage
        (N := N) e W b z| ≤
      ((cfzFamilyCarryBadPoints
        (N := N) (pairedDivisorLcm z)
        (fun q : SelectedCFZFormIndex e => q.1)).card : ℝ) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) +
        2 *
          (((N ^ Fintype.card (CFZVariable k) -
            (trimToMultiple (pairedDivisorLcm z) N) ^
              Fintype.card (CFZVariable k) : ℕ) : ℝ)) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) := by
  simpa only [selectedCFZCarryBlockEulerAverage] using
    abs_pairedDivisibilityDensity_cfz_sub_carryBlockEulerAverage_le_bad_add_boundary
      W b (fun q : SelectedCFZFormIndex e => q.1) z hz hDN

/-- Explicit `O_k(D/N)` estimate for every selected CFZ subfamily. -/
theorem
    abs_pairedDivisibilityDensity_selectedCFZ_sub_carryBlockEulerAverage_le_linear
    {k N : ℕ} [NeZero N]
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (W b : ℕ)
    (z : SelectedCFZFormIndex e → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (hz : SquarefreePairedDivisorChoice z)
    (hDN : pairedDivisorLcm z ≤ N) :
    |pairedDivisibilityDensity
        (fun q : SelectedCFZFormIndex e =>
          fun x : CubePoint k N =>
            cfzWTrickedLinearValue W b q.1 x)
        z -
      selectedCFZCarryBlockEulerAverage
        (N := N) e W b z| ≤
      (Fintype.card (SelectedCFZFormIndex e) : ℝ) *
          (2 * cfzCarryRange k + 1) *
          (2 * Fintype.card (CFZVariable k) * k + 1) *
          (pairedDivisorLcm z : ℝ) *
          (N : ℝ) ^
            (Fintype.card (CFZVariable k) - 1) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) +
        2 * (pairedDivisorLcm z : ℝ) *
          (Fintype.card (CFZVariable k) : ℝ) *
          (N : ℝ) ^
            (Fintype.card (CFZVariable k) - 1) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) := by
  simpa only [selectedCFZCarryBlockEulerAverage] using
    abs_pairedDivisibilityDensity_cfz_sub_carryBlockEulerAverage_le_linear
      hk W b (fun q : SelectedCFZFormIndex e => q.1) z hz hDN

/-- Collapsed `C_k D/N` form for every selected CFZ subfamily. -/
theorem
    abs_pairedDivisibilityDensity_selectedCFZ_sub_carryBlockEulerAverage_le_div
    {k N : ℕ} [NeZero N]
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (W b : ℕ)
    (z : SelectedCFZFormIndex e → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (hz : SquarefreePairedDivisorChoice z)
    (hDN : pairedDivisorLcm z ≤ N) :
    |pairedDivisibilityDensity
        (fun q : SelectedCFZFormIndex e =>
          fun x : CubePoint k N =>
            cfzWTrickedLinearValue W b q.1 x)
        z -
      selectedCFZCarryBlockEulerAverage
        (N := N) e W b z| ≤
      (cfzCarryBlockEulerErrorConstant k
          (Fintype.card (SelectedCFZFormIndex e)) : ℝ) *
        (pairedDivisorLcm z : ℝ) / (N : ℝ) := by
  simpa only [selectedCFZCarryBlockEulerAverage] using
    abs_pairedDivisibilityDensity_cfz_sub_carryBlockEulerAverage_le_div
      hk W b (fun q : SelectedCFZFormIndex e => q.1)
      z hz hDN

/-! ## Carry-dependent constants and primes dividing `W` -/

@[simp]
theorem cfzCarryAdjustedFamilyAtBlock_constant
    {κ : Type*} {k N : ℕ} [NeZero N]
    (D W b : ℕ) (forms : κ → CFZFormIndex k)
    (a : CFZVariable k → ℕ) (q : κ) :
    (cfzCarryAdjustedFamilyAtBlock
      (N := N) D W b forms a q).constant =
      (b : ℤ) - (W : ℤ) * (N : ℤ) *
        cfzCarry (N := N) (forms q) (fun v => D * a v) := by
  simp [cfzCarryAdjustedFamilyAtBlock]

@[simp]
theorem cfzCarryAdjustedFamilyAtBlock_coefficient
    {κ : Type*} {k N : ℕ} [NeZero N]
    (D W b : ℕ) (forms : κ → CFZFormIndex k)
    (a : CFZVariable k → ℕ) (q : κ)
    (v : CFZVariable k) :
    (cfzCarryAdjustedFamilyAtBlock
      (N := N) D W b forms a q).coefficient v =
      (W : ℤ) * cfzCoefficient (forms q) v := by
  simp [cfzCarryAdjustedFamilyAtBlock]

/-- Modulo a divisor of `W`, the carry correction and all linear
coefficients vanish, leaving the same reduced residue `b` on every block. -/
theorem cfzCarryAdjustedAffineForm_evalZMod_of_dvd
    {k p : ℕ} [NeZero p]
    (N W b : ℕ) (hpW : p ∣ W)
    (q : CFZFormIndex k) (c : ℤ)
    (x : CFZVariable k → ZMod p) :
    (cfzCarryAdjustedAffineForm N W b q c).evalZMod p x =
      (b : ZMod p) := by
  have hW : (W : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff W p).2 hpW
  unfold AffineForm.evalZMod AffineForm.linearMapZMod
  simp [hW]

/-- A carry-adjusted CFZ form has no zero modulo a prime dividing `W` when
`b` is reduced modulo `W`. -/
theorem cfzCarryAdjustedAffineForm_zeroFinsetZMod_eq_empty
    {k p : ℕ} [NeZero p]
    (N W b : ℕ)
    (hp : p.Prime) (hpW : p ∣ W) (hWb : W.Coprime b)
    (q : CFZFormIndex k) (c : ℤ) :
    (cfzCarryAdjustedAffineForm N W b q c).zeroFinsetZMod p =
      ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxzero :
      (cfzCarryAdjustedAffineForm N W b q c).evalZMod p x = 0 :=
    (AffineForm.mem_zeroFinsetZMod p
      (cfzCarryAdjustedAffineForm N W b q c) x).mp hx
  rw [cfzCarryAdjustedAffineForm_evalZMod_of_dvd
    N W b hpW q c x] at hxzero
  exact
    (natCast_ne_zero_of_prime_dvd_of_coprime
      hp hpW hWb) hxzero

/-- Thus every local avoidance factor on a carry block is literally the
unit factor at a prime dividing `W`. -/
theorem localAvoidanceProduct_cfzCarryAdjusted_eq_one_of_dvd
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k p : ℕ} [NeZero p]
    (N W b : ℕ)
    (hp : p.Prime) (hpW : p ∣ W) (hWb : W.Coprime b)
    (forms : κ → CFZFormIndex k) (c : κ → ℤ)
    (x : CFZVariable k → ZMod p) :
    localAvoidanceProduct p
        (fun q =>
          cfzCarryAdjustedAffineForm
            N W b (forms q) (c q))
        x = 1 := by
  simp [localAvoidanceProduct,
    cfzCarryAdjustedAffineForm_zeroFinsetZMod_eq_empty
      N W b hp hpW hWb]

/-- Dually, a nonempty common-zero density for a supported paired
divisibility condition is zero at a prime dividing `W`. -/
theorem affineFamilyZeroDensity_cfzCarryAdjusted_eq_zero_of_prime_dvd
    {κ : Type*} [DecidableEq κ]
    {k p : ℕ} [NeZero p]
    (N W b : ℕ)
    (hp : p.Prime) (hpW : p ∣ W) (hWb : W.Coprime b)
    (forms : κ → CFZFormIndex k) (c : κ → ℤ)
    (s : Finset κ) (hs : s.Nonempty) :
    affineFamilyZeroDensity p
        (fun q =>
          cfzCarryAdjustedAffineForm
            N W b (forms q) (c q))
        s = 0 := by
  unfold affineFamilyZeroDensity
  rw [show
      affineFamilyZeroProduct p
          (fun q =>
            cfzCarryAdjustedAffineForm
              N W b (forms q) (c q))
          s =
        fun _x => 0 by
      funext x
      obtain ⟨q, hq⟩ := hs
      unfold affineFamilyZeroProduct
      apply Finset.prod_eq_zero hq
      simp [finsetIndicator,
        cfzCarryAdjustedAffineForm_zeroFinsetZMod_eq_empty
          N W b hp hpW hWb]]
  exact mean_const (α := CFZVariable k → ZMod p) 0

/-- Prime-factor specialization: every supported carry-block local density
at a prime dividing `W` vanishes. -/
theorem cfzCarryBlockPrimeLocalDensity_eq_zero_of_dvd
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ) (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ)
    (hz : SquarefreePairedDivisorChoice z)
    (p : (pairedDivisorLcm z).primeFactors)
    (hpW : (p : ℕ) ∣ W) (hWb : W.Coprime b)
    (a : CFZVariable k → ℕ) :
    affineFamilyZeroDensity (p : ℕ)
        (cfzCarryAdjustedFamilyAtBlock
          (N := N) (pairedDivisorLcm z) W b forms a)
        (pairedPrimeSupport z p) = 0 := by
  have hpSupport :
      (p : ℕ).Prime ∧
        (pairedPrimeSupport z (p : ℕ)).Nonempty :=
    (mem_primeFactors_pairedDivisorLcm_iff
      hz (p : ℕ)).mp p.2
  exact
    affineFamilyZeroDensity_cfzCarryAdjusted_eq_zero_of_prime_dvd
      N W b hpSupport.1 hpW hWb forms
      (fun q =>
        cfzCarry (N := N) (forms q)
          (fun v => pairedDivisorLcm z * a v))
      (pairedPrimeSupport z p) hpSupport.2

/-- Selected-family specialization of the zero supported density at a
prime dividing `W`. -/
theorem selectedCFZCarryBlockPrimeLocalDensity_eq_zero_of_dvd
    {k N W : ℕ} [NeZero N]
    (e : LinearFormsExponent k) (b : ℕ)
    (z : SelectedCFZFormIndex e → ℕ × ℕ)
    (hz : SquarefreePairedDivisorChoice z)
    (p : (pairedDivisorLcm z).primeFactors)
    (hpW : (p : ℕ) ∣ W) (hWb : W.Coprime b)
    (a : CFZVariable k → ℕ) :
    affineFamilyZeroDensity (p : ℕ)
        (cfzCarryAdjustedFamilyAtBlock
          (N := N) (pairedDivisorLcm z) W b
          (fun q : SelectedCFZFormIndex e => q.1) a)
        (pairedPrimeSupport z p) = 0 := by
  exact
    cfzCarryBlockPrimeLocalDensity_eq_zero_of_dvd
      W b (fun q : SelectedCFZFormIndex e => q.1)
      z hz p hpW hWb a

/-- On every selected carry block, the local avoidance product is the unit
factor at a prime dividing `W`. -/
theorem selectedCFZCarryBlockLocalAvoidanceProduct_eq_one_of_dvd
    {k N W p : ℕ} [NeZero N] [NeZero p]
    (e : LinearFormsExponent k) (D b : ℕ)
    (hp : p.Prime) (hpW : p ∣ W) (hWb : W.Coprime b)
    (a : CFZVariable k → ℕ)
    (x : CFZVariable k → ZMod p) :
    localAvoidanceProduct p
        (cfzCarryAdjustedFamilyAtBlock
          (N := N) D W b
          (fun q : SelectedCFZFormIndex e => q.1) a)
        x = 1 := by
  exact
    localAvoidanceProduct_cfzCarryAdjusted_eq_one_of_dvd
      N W b hp hpW hWb
      (fun q : SelectedCFZFormIndex e => q.1)
      (fun q =>
        cfzCarry (N := N) q.1
          (fun v => D * a v))
      x

/-! ## Good primes outside `W` -/

/-- Carry corrections change only affine constants.  Every coefficient
minor is still scaled by `W²`. -/
@[simp]
theorem cfzCarryAdjustedAffineForm_coefficientMinor
    {k : ℕ} (N W b : ℕ)
    (q r : CFZFormIndex k) (c d : ℤ)
    (i j : CFZVariable k) :
    (cfzCarryAdjustedAffineForm N W b q c).coefficientMinor
        (cfzCarryAdjustedAffineForm N W b r d) i j =
      (W : ℤ) ^ 2 *
        (cfzAffineForm q).coefficientMinor
          (cfzAffineForm r) i j := by
  simp only [AffineForm.coefficientMinor,
    cfzCarryAdjustedAffineForm_coefficient,
    cfzAffineForm_coefficient]
  ring

/-- Direct modular one-form geometry survives arbitrary carry-dependent
integer constants whenever `p ∤ W`. -/
theorem affineNonzeroGoodPrime_cfzCarryAdjusted
    {κ : Type*} {k p : ℕ}
    (N W b : ℕ) (forms : κ → CFZFormIndex k)
    (c : κ → ℤ)
    (hgood : AffineNonzeroGoodPrime p
      (fun q => cfzAffineForm (forms q)))
    (hpW : ¬p ∣ W) :
    AffineNonzeroGoodPrime p
      (fun q =>
        cfzCarryAdjustedAffineForm
          N W b (forms q) (c q)) := by
  refine ⟨hgood.1, fun q => ?_⟩
  obtain ⟨i, hi⟩ := hgood.2 q
  refine ⟨i, ?_⟩
  have hw :=
    wTrickedAffineForm_coefficient_cast_ne_zero
      (W := W) (b := 0) (p := p)
      hgood.1 hpW (cfzAffineForm (forms q)) hi
  simpa only [cfzCarryAdjustedAffineForm_coefficient,
    wTrickedAffineForm_coefficient,
    cfzAffineForm_coefficient] using hw

/-- Direct modular rank-two geometry likewise survives arbitrary
carry-dependent constants whenever `p ∤ W`. -/
theorem affineRankTwoGoodPrime_cfzCarryAdjusted
    {κ : Type*} [Fintype κ]
    {k p : ℕ}
    (N W b : ℕ) (forms : κ → CFZFormIndex k)
    (c : κ → ℤ)
    (hgood : AffineRankTwoGoodPrime p
      (fun q => cfzAffineForm (forms q)))
    (hpW : ¬p ∣ W) :
    AffineRankTwoGoodPrime p
      (fun q =>
        cfzCarryAdjustedAffineForm
          N W b (forms q) (c q)) := by
  refine ⟨hgood.1, ?_⟩
  intro q r hqr
  obtain ⟨i, j, hij⟩ := hgood.2 hqr
  refine ⟨i, j, ?_⟩
  have hw :=
    wTrickedAffineForm_coefficientMinor_cast_ne_zero
      (W := W) (b := 0) (c := 0) (p := p)
      hgood.1 hpW
      (cfzAffineForm (forms q))
      (cfzAffineForm (forms r)) hij
  simpa only [cfzCarryAdjustedAffineForm_coefficientMinor,
    wTrickedAffineForm_coefficientMinor] using hw

/-- One-form and rank-two good-prime geometry determine every common-zero
density supported on at most two indices, for completely arbitrary affine
constants. -/
theorem affineFamilyZeroDensity_eq_inv_pow_card_of_goodPrime
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {p : ℕ} [NeZero p]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : AffineNonzeroGoodPrime p forms)
    (hrankTwo : AffineRankTwoGoodPrime p forms)
    (s : Finset κ) (hs : s.card ≤ 2) :
    affineFamilyZeroDensity p forms s =
      (1 : ℝ) / (p : ℝ) ^ s.card := by
  rcases Nat.eq_zero_or_pos s.card with hzero | hpos
  · have hs0 : s = ∅ := Finset.card_eq_zero.mp hzero
    subst s
    simp
  · have hcard : s.card = 1 ∨ s.card = 2 := by
      omega
    rcases hcard with hone | htwo
    · obtain ⟨q, rfl⟩ := Finset.card_eq_one.mp hone
      simpa using
        affineFamilyZeroDensity_singleton_of_nonzeroGoodPrime
          hnonzero q
    · obtain ⟨q, r, hqr, rfl⟩ :=
        Finset.card_eq_two.mp htwo
      have hcard : ({q, r} : Finset κ).card = 2 :=
        Finset.card_eq_two.mpr ⟨q, r, hqr, rfl⟩
      rw [hcard, affineFamilyZeroDensity_pair p forms hqr]
      obtain ⟨i, j, hij⟩ := hrankTwo.2 hqr
      exact
        AffineForm.mean_zeroFinsetZMod_mul
          hrankTwo.1 (forms q) (forms r) hij

/-- Above the ambient CFZ exceptional cutoff and outside `W`, every selected
carry block has direct modular one-form and rank-two geometry. -/
theorem selectedCFZCarryAdjustedFamilyAtBlock_goodPrime
    {k N W p : ℕ} [NeZero N]
    (hk : 2 ≤ k) (hp : p.Prime) (hpW : ¬p ∣ W)
    (hlarge :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) < p)
    (e : LinearFormsExponent k) (D b : ℕ)
    (a : CFZVariable k → ℕ) :
    AffineNonzeroGoodPrime p
        (cfzCarryAdjustedFamilyAtBlock
          (N := N) D W b
          (fun q : SelectedCFZFormIndex e => q.1) a) ∧
      AffineRankTwoGoodPrime p
        (cfzCarryAdjustedFamilyAtBlock
          (N := N) D W b
          (fun q : SelectedCFZFormIndex e => q.1) a) := by
  change
    AffineNonzeroGoodPrime p
        (fun q : SelectedCFZFormIndex e =>
          cfzCarryAdjustedAffineForm N W b q.1
            (cfzCarry (N := N) q.1
              (fun v => D * a v))) ∧
      AffineRankTwoGoodPrime p
        (fun q : SelectedCFZFormIndex e =>
          cfzCarryAdjustedAffineForm N W b q.1
            (cfzCarry (N := N) q.1
              (fun v => D * a v)))
  let c : SelectedCFZFormIndex e → ℤ :=
    fun q =>
      cfzCarry (N := N) q.1 (fun v => D * a v)
  have hnonzero :=
    affineNonzeroGoodPrime_cfzCarryAdjusted
      N W b
      (fun q : SelectedCFZFormIndex e => q.1) c
      (selectedCFZAffineNonzeroGoodPrime
        hk hp hlarge e)
      hpW
  have hrank :=
    affineRankTwoGoodPrime_cfzCarryAdjusted
      N W b
      (fun q : SelectedCFZFormIndex e => q.1) c
      (selectedCFZAffineRankTwoGoodPrime
        hk hp hlarge e)
      hpW
  simpa only [c] using And.intro hnonzero hrank

/-- Exact empty/singleton/pair local density on every selected carry block
at a good prime outside `W`. -/
theorem
    selectedCFZCarryBlockPrimeLocalDensity_eq_inv_pow_card_of_card_le_two
    {k N W : ℕ} [NeZero N]
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k) (b : ℕ)
    (z : SelectedCFZFormIndex e → ℕ × ℕ)
    (p : (pairedDivisorLcm z).primeFactors)
    (hpW : ¬(p : ℕ) ∣ W)
    (hlarge :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) <
        (p : ℕ))
    (a : CFZVariable k → ℕ)
    (hsupport : (pairedPrimeSupport z p).card ≤ 2) :
    affineFamilyZeroDensity (p : ℕ)
        (cfzCarryAdjustedFamilyAtBlock
          (N := N) (pairedDivisorLcm z) W b
          (fun q : SelectedCFZFormIndex e => q.1) a)
        (pairedPrimeSupport z p) =
      (1 : ℝ) / (p : ℝ) ^
        (pairedPrimeSupport z p).card := by
  have hp : (p : ℕ).Prime :=
    Nat.prime_of_mem_primeFactors p.2
  obtain ⟨hnonzero, hrank⟩ :=
    selectedCFZCarryAdjustedFamilyAtBlock_goodPrime
      (N := N) (W := W) (p := (p : ℕ))
      hk hp hpW hlarge e (pairedDivisorLcm z) b a
  exact
    affineFamilyZeroDensity_eq_inv_pow_card_of_goodPrime
      (p := (p : ℕ))
      hnonzero hrank (pairedPrimeSupport z p) hsupport

/-- Every nontrivial selected carry-block local density is at most `p⁻²`
at a good prime outside `W`. -/
theorem
    selectedCFZCarryBlockPrimeLocalDensity_le_inv_sq_of_nontrivial
    {k N W : ℕ} [NeZero N]
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k) (b : ℕ)
    (z : SelectedCFZFormIndex e → ℕ × ℕ)
    (p : (pairedDivisorLcm z).primeFactors)
    (hpW : ¬(p : ℕ) ∣ W)
    (hlarge :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) <
        (p : ℕ))
    (a : CFZVariable k → ℕ)
    (hsupport : (pairedPrimeSupport z p).Nontrivial) :
    affineFamilyZeroDensity (p : ℕ)
        (cfzCarryAdjustedFamilyAtBlock
          (N := N) (pairedDivisorLcm z) W b
          (fun q : SelectedCFZFormIndex e => q.1) a)
        (pairedPrimeSupport z p) ≤
      (1 : ℝ) / (p : ℝ) ^ 2 := by
  have hp : (p : ℕ).Prime :=
    Nat.prime_of_mem_primeFactors p.2
  obtain ⟨_hnonzero, hrank⟩ :=
    selectedCFZCarryAdjustedFamilyAtBlock_goodPrime
      (N := N) (W := W) (p := (p : ℕ))
      hk hp hpW hlarge e (pairedDivisorLcm z) b a
  exact
    affineFamilyZeroDensity_le_inv_sq_of_goodPrime
      (p := (p : ℕ))
      hrank (pairedPrimeSupport z p) hsupport

/-- Singleton specialization of the selected carry-block good-prime
formula. -/
theorem selectedCFZCarryBlockPrimeLocalDensity_eq_inv_of_card_eq_one
    {k N W : ℕ} [NeZero N]
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k) (b : ℕ)
    (z : SelectedCFZFormIndex e → ℕ × ℕ)
    (p : (pairedDivisorLcm z).primeFactors)
    (hpW : ¬(p : ℕ) ∣ W)
    (hlarge :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) <
        (p : ℕ))
    (a : CFZVariable k → ℕ)
    (hsupport : (pairedPrimeSupport z p).card = 1) :
    affineFamilyZeroDensity (p : ℕ)
        (cfzCarryAdjustedFamilyAtBlock
          (N := N) (pairedDivisorLcm z) W b
          (fun q : SelectedCFZFormIndex e => q.1) a)
        (pairedPrimeSupport z p) =
      (1 : ℝ) / (p : ℝ) := by
  have hle : (pairedPrimeSupport z p).card ≤ 2 := by
    omega
  simpa [hsupport] using
    selectedCFZCarryBlockPrimeLocalDensity_eq_inv_pow_card_of_card_le_two
      (N := N) (W := W)
      hk e b z p hpW hlarge a hle

/-- Two-form specialization of the selected carry-block good-prime
formula. -/
theorem selectedCFZCarryBlockPrimeLocalDensity_eq_inv_sq_of_card_eq_two
    {k N W : ℕ} [NeZero N]
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k) (b : ℕ)
    (z : SelectedCFZFormIndex e → ℕ × ℕ)
    (p : (pairedDivisorLcm z).primeFactors)
    (hpW : ¬(p : ℕ) ∣ W)
    (hlarge :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) <
        (p : ℕ))
    (a : CFZVariable k → ℕ)
    (hsupport : (pairedPrimeSupport z p).card = 2) :
    affineFamilyZeroDensity (p : ℕ)
        (cfzCarryAdjustedFamilyAtBlock
          (N := N) (pairedDivisorLcm z) W b
          (fun q : SelectedCFZFormIndex e => q.1) a)
        (pairedPrimeSupport z p) =
      (1 : ℝ) / (p : ℝ) ^ 2 := by
  have hle : (pairedPrimeSupport z p).card ≤ 2 := by
    omega
  simpa [hsupport] using
    selectedCFZCarryBlockPrimeLocalDensity_eq_inv_pow_card_of_card_le_two
      (N := N) (W := W)
      hk e b z p hpW hlarge a hle

end Wikipedia.SzemeredisTheorem
