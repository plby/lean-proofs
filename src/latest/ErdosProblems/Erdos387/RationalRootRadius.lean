/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RationalClosedPoints
import Waring.Analytic.BoundedPowerSums
import Mathlib.Algebra.Order.BigOperators.Group.Multiset

/-!
# Conditional square-root radius for the rational Artin polynomial

The Euler and closed-point identities reduce the rational Weil bound to one
uniform estimate over the even finite-field extensions.  This file makes the
last reduction literal: a bound `C * p ^ m`, uniform in `m`, bounds every
reciprocal root by `sqrt p`.  It then derives the corresponding degree-one
complete-sum estimate.
-/

namespace Erdos387

open Polynomial
open scoped BigOperators

namespace RationalWeil

/-- The exact remaining analytic input for the rational Artin polynomial:
the zero-extended trace sums in every sufficiently large even extension have
square-root size, with a constant independent of the extension degree. -/
def HasEvenExtensionSquareRootBound
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) : Prop :=
  ∃ C : ℝ, ∀ (m : ℕ) (hm : 3 ≤ m),
    letI : NeZero (2 * m) := ⟨by omega⟩
    let E := FiniteField.Extension (ZMod p) p (2 * m)
    letI : Fintype E := Fintype.ofFinite E
    ‖∑ x : E, zeroExtendedTraceWeight coeff x‖ ≤
      C * (p : ℝ) ^ m

/-- An extension-uniform square-root estimate puts every reciprocal root of
the rational Artin polynomial in the closed disk of radius `sqrt p`. -/
theorem norm_reverse_artinLPolynomial_root_le_sqrt_of_evenExtensionBound
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty)
    (hbound : HasEvenExtensionSquareRootBound coeff) :
    ∀ z ∈ (artinLPolynomial coeff).reverse.roots,
      ‖z‖ ≤ Real.sqrt (p : ℝ) := by
  obtain ⟨C, hC⟩ := hbound
  let roots := (artinLPolynomial coeff).reverse.roots
  have hpReal : (0 : ℝ) < p := by
    exact_mod_cast (Fact.out : p.Prime).pos
  have hpowers : ∀ m, 3 ≤ m →
      ‖(roots.map fun z ↦ z ^ (2 * m)).sum‖ ≤
        C * (p : ℝ) ^ m := by
    intro m hm
    letI : NeZero (2 * m) := ⟨by omega⟩
    let E := FiniteField.Extension (ZMod p) p (2 * m)
    letI : Fintype E := Fintype.ofFinite E
    have hexact := extensionTraceSum_eq_neg_artinRootPowerSum
      p (2 * m) coeff hne
    have hsum := hC m hm
    dsimp only at hsum
    calc
      ‖(roots.map fun z ↦ z ^ (2 * m)).sum‖ =
          ‖-((roots.map fun z ↦ z ^ (2 * m)).sum)‖ :=
        (norm_neg _).symm
      _ = ‖∑ x : E, zeroExtendedTraceWeight coeff x‖ := by
        exact congrArg norm hexact.symm
      _ ≤ C * (p : ℝ) ^ m := hsum
  have hradius :=
    Waring.Analytic.Weil.norm_le_sqrt_of_bounded_even_multisetPowerSums
      roots hpReal 3 hpowers
  exact hradius

/-- The arbitrary finite-extension version of the closed-point identity.
This specializes the generic conjugacy-class reindexing, and is useful in
degree one without choosing a model of the finite field. -/
theorem finiteExtensionTraceSum_eq_neg_artinRootPowerSum
    (p n : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (L : Type*) [Field L] [Finite L] [Algebra (ZMod p) L]
    [FiniteDimensional (ZMod p) L]
    (hfin : Module.finrank (ZMod p) L = n)
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty) :
    letI : Fintype L := Fintype.ofFinite L
    (∑ x : L, zeroExtendedTraceWeight coeff x) =
      -((artinLPolynomial coeff).reverse.roots.map
        (fun a ↦ a ^ n)).sum := by
  classical
  letI : Fintype L := Fintype.ofFinite L
  calc
    (∑ x : L, zeroExtendedTraceWeight coeff x) =
        ∑ x : L, polynomialWeight coeff (minpoly (ZMod p) x) ^
          (n / (minpoly (ZMod p) x).natDegree) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← extensionPointWeight_eq_zeroExtendedTraceWeight coeff x]
      simp only [extensionPointWeight, hfin]
    _ = ∑ P : MonicIrreducibleLE (ZMod p) n,
        if P.poly.natDegree ∣ n then
          (P.poly.natDegree : ℂ) *
            polynomialWeight coeff P.poly ^ (n / P.poly.natDegree)
        else 0 := by
      simpa only [nsmul_eq_mul] using
        (sum_finiteExtension_eq_irreducibleSum
          (ZMod p) n L hfin
          (fun P : (ZMod p)[X] ↦
            polynomialWeight coeff P ^ (n / P.natDegree)))
    _ = -((artinLPolynomial coeff).reverse.roots.map
          (fun a ↦ a ^ n)).sum :=
      irreducible_sum_eq_neg_artinRootPowerSum
        coeff hne le_rfl (NeZero.ne n)

/-- Over the base field, the mapped simple-pole phase is the original
finite partial-fraction phase. -/
theorem mappedSimplePolePhase_self
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (x : ZMod p) :
    mappedSimplePolePhase coeff x =
      InverseRational.simplePolePhase coeff x := by
  rw [InverseRational.simplePolePhase_eq_sum_poleSupport]
  simp [mappedSimplePolePhase]

/-- In the base field, being an embedded pole is just membership in the
original pole support. -/
theorem isMappedPole_self_iff
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (x : ZMod p) :
    IsMappedPole coeff x ↔ x ∈ InverseRational.poleSupport coeff := by
  constructor
  · rintro ⟨r, hr, hxr⟩
    have hxr' : x = r := by simpa using hxr
    simpa [hxr'] using hr
  · intro hx
    exact ⟨x, hx, by simp⟩

/-- The abstract trace weight reduces over the prime field to the literal
zero extension of the original rational phase. -/
theorem zeroExtendedTraceWeight_self
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (x : ZMod p) :
    zeroExtendedTraceWeight coeff x =
      if x ∈ InverseRational.poleSupport coeff then 0
      else ZMod.stdAddChar (InverseRational.simplePolePhase coeff x) := by
  rw [zeroExtendedTraceWeight]
  by_cases hx : x ∈ InverseRational.poleSupport coeff
  · rw [if_pos ((isMappedPole_self_iff coeff x).2 hx), if_pos hx]
  · rw [if_neg (fun h ↦ hx ((isMappedPole_self_iff coeff x).1 h)),
      if_neg hx, Algebra.trace_self_apply, mappedSimplePolePhase_self]

/-- In degree one the zero-extended rational trace weight has the exact
reciprocal-root power-sum identity. -/
theorem baseTraceSum_eq_neg_artinRootSum
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty) :
    (∑ x : ZMod p, zeroExtendedTraceWeight coeff x) =
      -(artinLPolynomial coeff).reverse.roots.sum := by
  have h := finiteExtensionTraceSum_eq_neg_artinRootPowerSum
    p 1 (ZMod p) (by simp) coeff hne
  let finiteFintype : Fintype (ZMod p) := Fintype.ofFinite (ZMod p)
  have h' :
      (@Finset.univ (ZMod p) finiteFintype).sum
          (fun x ↦ zeroExtendedTraceWeight coeff x) =
        -(artinLPolynomial coeff).reverse.roots.sum := by
    simpa only [pow_one, Multiset.map_id'] using h
  let standardUniv : Finset (ZMod p) :=
    @Finset.univ (ZMod p) (ZMod.fintype p)
  let finiteUniv : Finset (ZMod p) :=
    @Finset.univ (ZMod p) finiteFintype
  have huniv :
      standardUniv = finiteUniv := by
    dsimp only [standardUniv, finiteUniv]
    ext x
    simp only [Finset.mem_univ]
  change standardUniv.sum (fun x ↦ zeroExtendedTraceWeight coeff x) = _
  rw [huniv]
  exact h'

/-- Conditional rational Weil bound in the precise zero-extended form.  The
factor is the checked strict degree bound for the Artin polynomial. -/
theorem norm_baseTraceSum_le_of_evenExtensionBound
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty)
    (hbound : HasEvenExtensionSquareRootBound coeff) :
    ‖∑ x : ZMod p, zeroExtendedTraceWeight coeff x‖ ≤
      ((2 * (InverseRational.poleSupport coeff).card - 1 : ℕ) : ℝ) *
        Real.sqrt (p : ℝ) := by
  let roots := (artinLPolynomial coeff).reverse.roots
  have hradius : ∀ z ∈ roots, ‖z‖ ≤ Real.sqrt (p : ℝ) :=
    norm_reverse_artinLPolynomial_root_le_sqrt_of_evenExtensionBound
      coeff hne hbound
  have hcardLt : roots.card <
      2 * (InverseRational.poleSupport coeff).card := by
    simpa only [roots] using
      card_roots_reverse_artinLPolynomial_lt coeff hne
  have hcard : roots.card ≤
      2 * (InverseRational.poleSupport coeff).card - 1 := by omega
  have hsumNorm :
      (roots.map fun z ↦ ‖z‖).sum ≤
        roots.card • Real.sqrt (p : ℝ) := by
    have hmapped := Multiset.sum_le_card_nsmul
      (roots.map fun z ↦ ‖z‖) (Real.sqrt (p : ℝ)) (by
        intro r hr
        obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hr
        exact hradius z hz)
    simpa only [Multiset.card_map] using hmapped
  have hidentity := baseTraceSum_eq_neg_artinRootSum coeff hne
  rw [hidentity, norm_neg]
  calc
    ‖roots.sum‖ ≤ (roots.map fun z ↦ ‖z‖).sum :=
      norm_multiset_sum_le roots
    _ ≤ roots.card • Real.sqrt (p : ℝ) := hsumNorm
    _ = (roots.card : ℝ) * Real.sqrt (p : ℝ) := by
      rw [nsmul_eq_mul]
    _ ≤ ((2 * (InverseRational.poleSupport coeff).card - 1 : ℕ) : ℝ) *
        Real.sqrt (p : ℝ) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (Real.sqrt_nonneg _)

/-- Conditional rational Weil bound stated directly for the original
simple-pole phase, with its supported poles assigned weight zero. -/
theorem norm_zeroExtendedSimplePolePhase_sum_le_of_evenExtensionBound
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty)
    (hbound : HasEvenExtensionSquareRootBound coeff) :
    ‖∑ x : ZMod p,
        if x ∈ InverseRational.poleSupport coeff then 0
        else ZMod.stdAddChar (InverseRational.simplePolePhase coeff x)‖ ≤
      ((2 * (InverseRational.poleSupport coeff).card - 1 : ℕ) : ℝ) *
        Real.sqrt (p : ℝ) := by
  have h := norm_baseTraceSum_le_of_evenExtensionBound coeff hne hbound
  simpa only [zeroExtendedTraceWeight_self] using h

end RationalWeil

end Erdos387
