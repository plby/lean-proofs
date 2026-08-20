import ErdosProblems.Erdos980.ElliottTail.OddInertAuxiliaryPrimes
import ErdosProblems.Erdos980.ElliottTail.LocalNormEuler

/-!
# Exact inert power-class cells in fixed-ideal coordinates

For a finite family `Q` of the inert auxiliary primes, the rational moduli are
pairwise coprime.  For a fixed correction ideal `J`, reduction of its integral
coordinates modulo each `q \in Q` is a bijection onto the corresponding local
residue field.  Elementary Chinese remaindering of the scalar coordinates then
embeds the product of local unit groups in the full coordinate vectors modulo
the product.

Restricting the CRT map to local units gives an embedding of the product of
local unit groups in the coordinate vectors.  Each local unit group is cyclic
and its quotient by `ell`-th powers has exactly `ell` elements.  Consequently
one prescribed tensor of local power classes occupies exactly an
`ell ^ (-#Q)` fraction of the full local-unit tuples.  The final theorem is
stated without division, in precisely the form consumed by
`RayNormRemainder.exists_uniform_combinedRayUnitNormCellCount_of_primeBounds`.
-/

open scoped BigOperators NumberField nonZeroDivisors

noncomputable section

namespace Erdos980.ElliottTail.OddInertTensorCells

open Function NumberField Ideal
open NumberFieldLargerSieve
open OddInertAuxiliaryPrimes
open LocalNormEuler

variable (ell : ℕ) [Fact ell.Prime]
variable (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {ell} ℚ K]

/-- The scalar product modulus of a finite auxiliary-prime family. -/
def inertTensorModulus (Q : Finset ℕ) : ℕ := ∏ q : Q, q.1

/-- The local quotient ring at one member of the selected family. -/
abbrev InertLocalRing (Q : Finset ℕ) (q : Q) :=
  𝓞 K ⧸ rationalModulusIdeal K q.1

/-- The local unit group at one member of the selected family. -/
abbrev InertLocalUnits (Q : Finset ℕ) (q : Q) :=
  (InertLocalRing K Q q)ˣ

private theorem inertTensorModulus_ne_zero
    (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime) :
    inertTensorModulus Q ≠ 0 := by
  unfold inertTensorModulus
  exact Finset.prod_ne_zero_iff.mpr fun q _ ↦ (hprime q.1 q.2).ne_zero

private theorem inertTensorModuli_pairwise_coprime
    (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime) :
    Pairwise (Nat.Coprime on fun q : Q ↦ q.1) := by
  intro q r hqr
  exact (Nat.coprime_primes (hprime q.1 q.2) (hprime r.1 r.2)).mpr
    (Subtype.coe_ne_coe.mpr hqr)

/-- Local unit tuples embedded into the integral coordinate vectors of a
fixed correction ideal.  This is an embedding, not an equivalence: it lands
exactly in the full-unit residue tuples inside all coordinate vectors. -/
noncomputable def inertLocalUnitsCoordinateEmbedding
    (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (J : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q ∈ Q, q.Coprime (Ideal.absNorm (J : Ideal (𝓞 K)))) :
    (∀ q : Q, InertLocalUnits K Q q) ↪
      (NumberField.mixedEmbedding.index K → ZMod (inertTensorModulus Q)) := by
  letI : NeZero (inertTensorModulus Q) :=
    ⟨inertTensorModulus_ne_zero Q hprime⟩
  let hpair := inertTensorModuli_pairwise_coprime Q hprime
  let eCRT := ZMod.prodEquivPi (fun q : Q ↦ q.1) hpair
  refine
    { toFun := fun u i ↦ eCRT.symm (fun q ↦
        (fixedIdealCoordinateQuotientEquiv K J q.1
          (hprime q.1 q.2) (hcop q.1 q.2)).symm
          (u q : InertLocalRing K Q q) i)
      inj' := ?_ }
  intro u v huv
  funext q
  apply Units.ext
  let eCoord := fixedIdealCoordinateQuotientEquiv K J q.1
    (hprime q.1 q.2) (hcop q.1 q.2)
  apply eCoord.symm.injective
  funext i
  have hi := congrFun huv i
  have hqi := congrArg (fun z ↦ eCRT z q) hi
  rw [eCRT.apply_symm_apply, eCRT.apply_symm_apply] at hqi
  exact hqi

/-- One prescribed tensor of local `ell`-power classes, transported into
the fixed-ideal coordinate residue space. -/
noncomputable def inertPowerClassCoordinateCell
    (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (J : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q ∈ Q, q.Coprime (Ideal.absNorm (J : Ideal (𝓞 K))))
    (pattern : PowerClassTensor Q (InertLocalUnits K Q) ell) :
    Finset (NumberField.mixedEmbedding.index K →
      ZMod (inertTensorModulus Q)) := by
  classical
  letI (q : Q) : NeZero (rationalModulusIdeal K q.1) :=
    ⟨rationalModulusIdeal_ne_bot (hprime q.1 q.2).ne_zero⟩
  letI (q : Q) : Finite (InertLocalRing K Q q) :=
    Ring.HasFiniteQuotients.finiteQuotient
      (rationalModulusIdeal_ne_bot (hprime q.1 q.2).ne_zero)
  letI : ∀ q : Q, Fintype (InertLocalUnits K Q q) :=
    fun _ ↦ Fintype.ofFinite _
  exact mappedPowerClassTensorResidueCell
    (inertLocalUnitsCoordinateEmbedding K Q hprime J hcop) ell pattern

/-- The number of all full local-unit tuples for `Q`. -/
noncomputable def inertUnitResidueCount
    (Q : Finset ℕ) : ℕ :=
  Nat.card (∀ q : Q, InertLocalUnits K Q q)

/-- Exact denominator-free density certificate for the transported cell.
Every selected prime is inert, so each local cyclic unit group has exactly
`ell` power classes. -/
theorem ell_pow_mul_inertPowerClassCoordinateCell_card
    {t : ℕ} (Q : Finset ℕ)
    (hQ : Q ⊆ inertAuxiliaryPrimes ell t)
    (J : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q ∈ Q, q.Coprime (Ideal.absNorm (J : Ideal (𝓞 K))))
    (pattern : PowerClassTensor Q (InertLocalUnits K Q) ell) :
    ell ^ Q.card *
        (inertPowerClassCoordinateCell ell K Q
          (fun q hq ↦ inertAuxiliaryPrimes_prime ell (hQ hq))
          J hcop pattern).card =
      inertUnitResidueCount K Q := by
  classical
  let hprime : ∀ q ∈ Q, q.Prime :=
    fun q hq ↦ inertAuxiliaryPrimes_prime ell (hQ hq)
  letI (q : Q) : NeZero (rationalModulusIdeal K q.1) :=
    ⟨rationalModulusIdeal_ne_bot (hprime q.1 q.2).ne_zero⟩
  letI (q : Q) : Finite (InertLocalRing K Q q) :=
    Ring.HasFiniteQuotients.finiteQuotient
      (rationalModulusIdeal_ne_bot (hprime q.1 q.2).ne_zero)
  letI : ∀ q : Q, Fintype (InertLocalUnits K Q q) :=
    fun _ ↦ Fintype.ofFinite _
  letI : ∀ q : Q, IsCyclic (InertLocalUnits K Q q) :=
    fun q ↦ inertAuxiliaryPrimes_quotient_units_isCyclic
      ell (K := K) (hQ q.2)
  have hellDvd : ∀ q : Q, ell ∣ Fintype.card (InertLocalUnits K Q q) := by
    intro q
    have hnat : ell ∣ Nat.card
        ((𝓞 K ⧸ Ideal.span {(q.1 : 𝓞 K)})ˣ) :=
      inertAuxiliaryPrimes_ell_dvd_quotient_units_natCard
        ell (K := K) (hQ q.2)
    change ell ∣ Nat.card (InertLocalUnits K Q q) at hnat
    rw [Nat.card_eq_fintype_card] at hnat
    exact hnat
  simpa only [inertPowerClassCoordinateCell, inertUnitResidueCount,
    Nat.card_eq_fintype_card, Fintype.card_coe] using
    (ell_pow_mul_mappedPowerClassTensorResidueCell_card
      hellDvd
      (inertLocalUnitsCoordinateEmbedding K Q hprime J hcop)
      pattern)

end Erdos980.ElliottTail.OddInertTensorCells
