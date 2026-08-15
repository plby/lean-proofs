/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RationalEulerRootIdentity
import ErdosProblems.Erdos387.RationalTraceBridge
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Minpoly.ConjRootClass

/-!
# Closed points for the rational Artin weight

Conjugacy classes in the chosen degree-`n` finite-field extension are
equivalent to monic irreducibles whose degrees divide `n`.  Fiberwise
reindexing therefore identifies the extension-point sum with the Euler sum.
-/

namespace Erdos387

open Polynomial
open scoped BigOperators

namespace RationalWeil

def ExtensionClosedPoint (K : Type*) [Field K] (n : Nat) :=
  {P : MonicIrreducibleLE K n // P.poly.natDegree ∣ n}

namespace ExtensionClosedPoint

variable {K : Type*} [Field K] {n : Nat}

def poly (P : ExtensionClosedPoint K n) : K[X] := P.1.poly

theorem monic (P : ExtensionClosedPoint K n) : P.poly.Monic := P.1.monic

theorem irreducible (P : ExtensionClosedPoint K n) : Irreducible P.poly :=
  P.1.irreducible

theorem natDegree_dvd (P : ExtensionClosedPoint K n) : P.poly.natDegree ∣ n :=
  P.2

end ExtensionClosedPoint

variable (K : Type*) [Field K] [Fintype K]
variable (p n : Nat) [Fact p.Prime] [CharP K p] [NeZero n]

noncomputable local instance : Fintype (FiniteField.Extension K p n) :=
  Fintype.ofFinite _

private noncomputable def conjugacyClassClosedPoint
    (c : ConjRootClass K (FiniteField.Extension K p n)) :
    ExtensionClosedPoint K n := by
  let P : K[X] := c.minpoly
  have hdiv : P.natDegree ∣ n := by
    rw [← FiniteField.finrank_extension K p n]
    exact c.irreducible_minpoly.natDegree_dvd_finrank c.splits_minpoly
  exact
    ⟨{ poly := P
       irreducible := c.irreducible_minpoly
       monic := c.monic_minpoly
       natDegree_le := Nat.le_of_dvd (NeZero.pos n) hdiv }, hdiv⟩

private theorem conjugacyClassClosedPoint_injective :
    Function.Injective (conjugacyClassClosedPoint K p n) := by
  intro c d h
  apply ConjRootClass.minpoly_injective
  exact congrArg (fun P : ExtensionClosedPoint K n ↦ P.poly) h

private theorem exists_minpoly_eq_closedPoint
    (P : ExtensionClosedPoint K n) :
    ∃ x : FiniteField.Extension K p n, minpoly K x = P.poly := by
  letI : Fact (Irreducible P.poly) := ⟨P.irreducible⟩
  have hfinrank : Module.finrank K (AdjoinRoot P.poly) = P.poly.natDegree := by
    rw [(AdjoinRoot.powerBasis P.irreducible.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim]
  have hdvd : Module.finrank K (AdjoinRoot P.poly) ∣
      Module.finrank K (FiniteField.Extension K p n) := by
    rw [hfinrank, FiniteField.finrank_extension K p n]
    exact P.natDegree_dvd
  let f : AdjoinRoot P.poly →ₐ[K] FiniteField.Extension K p n :=
    (FiniteField.nonempty_algHom_of_finrank_dvd hdvd).some
  let x : FiniteField.Extension K p n := f (AdjoinRoot.root P.poly)
  refine ⟨x, ?_⟩
  have hroot : aeval (AdjoinRoot.root P.poly) P.poly = 0 := by
    rw [Polynomial.aeval_def]
    exact AdjoinRoot.eval₂_root P.poly
  have hminpoly : minpoly K (AdjoinRoot.root P.poly) = P.poly := by
    have h := minpoly.eq_of_irreducible P.irreducible hroot
    simpa [P.monic.leadingCoeff] using h.symm
  calc
    minpoly K x = minpoly K (AdjoinRoot.root P.poly) :=
      minpoly.algHom_eq f f.injective _
    _ = P.poly := hminpoly

private theorem conjugacyClassClosedPoint_surjective :
    Function.Surjective (conjugacyClassClosedPoint K p n) := by
  intro P
  obtain ⟨x, hx⟩ := exists_minpoly_eq_closedPoint K p n P
  refine ⟨ConjRootClass.mk K x, ?_⟩
  apply Subtype.ext
  apply MonicIrreducibleLE.poly_injective
  exact hx

noncomputable def conjugacyClassEquivClosedPoint :
    ConjRootClass K (FiniteField.Extension K p n) ≃ ExtensionClosedPoint K n :=
  Equiv.ofBijective (conjugacyClassClosedPoint K p n)
    ⟨conjugacyClassClosedPoint_injective K p n,
      conjugacyClassClosedPoint_surjective K p n⟩

noncomputable local instance : Fintype (ExtensionClosedPoint K n) := by
  unfold ExtensionClosedPoint
  infer_instance

noncomputable local instance :
    Fintype (ConjRootClass K (FiniteField.Extension K p n)) :=
  Fintype.ofEquiv (ExtensionClosedPoint K n)
    (conjugacyClassEquivClosedPoint K p n).symm

noncomputable local instance
    (c : ConjRootClass K (FiniteField.Extension K p n)) : Fintype c.carrier :=
  Fintype.ofFinite _

theorem card_conjugacyClass_carrier
    (c : ConjRootClass K (FiniteField.Extension K p n)) :
    Fintype.card c.carrier = c.minpoly.natDegree := by
  calc
    Fintype.card c.carrier = Fintype.card (c.minpoly.rootSet
        (FiniteField.Extension K p n)) :=
      Fintype.card_congr
        (Equiv.setCongr c.rootSet_minpoly_eq_carrier).symm
    _ = c.minpoly.natDegree :=
      Polynomial.card_rootSet_eq_natDegree c.separable_minpoly c.splits_minpoly

theorem sum_extension_eq_sum_conjugacyClasses
    {A : Type*} [AddCommMonoid A] (f : K[X] → A) :
    (∑ x : FiniteField.Extension K p n, f (minpoly K x)) =
      ∑ c : ConjRootClass K (FiniteField.Extension K p n),
        c.minpoly.natDegree • f c.minpoly := by
  classical
  rw [← Fintype.sum_fiberwise (ConjRootClass.mk K)
    (fun x : FiniteField.Extension K p n ↦ f (minpoly K x))]
  apply Finset.sum_congr rfl
  intro c hc
  calc
    (∑ x : {x : FiniteField.Extension K p n // ConjRootClass.mk K x = c},
        f (minpoly K x.1)) =
        ∑ _x : {x : FiniteField.Extension K p n //
          ConjRootClass.mk K x = c}, f c.minpoly := by
      apply Fintype.sum_congr
      intro x
      rw [← ConjRootClass.minpoly_mk (K := K) x.1, x.2]
    _ = Fintype.card {x : FiniteField.Extension K p n //
          ConjRootClass.mk K x = c} • f c.minpoly := by
      simp
    _ = Fintype.card c.carrier • f c.minpoly := by
      congr 1
      apply Fintype.card_congr
      exact
        { toFun := fun x ↦ ⟨x.1, x.2⟩
          invFun := fun x ↦ ⟨x.1, x.2⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
    _ = c.minpoly.natDegree • f c.minpoly := by
      rw [card_conjugacyClass_carrier K p n c]

theorem sum_extension_eq_irreducibleSum
    {A : Type*} [AddCommMonoid A] (f : K[X] → A) :
    (∑ x : FiniteField.Extension K p n, f (minpoly K x)) =
      ∑ P : MonicIrreducibleLE K n,
        if P.poly.natDegree ∣ n then P.poly.natDegree • f P.poly else 0 := by
  classical
  rw [sum_extension_eq_sum_conjugacyClasses K p n]
  calc
    (∑ c : ConjRootClass K (FiniteField.Extension K p n),
        c.minpoly.natDegree • f c.minpoly) =
        ∑ P : ExtensionClosedPoint K n, P.poly.natDegree • f P.poly := by
      exact (conjugacyClassEquivClosedPoint K p n).sum_comp
        (fun P ↦ P.poly.natDegree • f P.poly)
    _ = ∑ P ∈ (Finset.univ : Finset (MonicIrreducibleLE K n)).filter
          (fun P ↦ P.poly.natDegree ∣ n), P.poly.natDegree • f P.poly := by
      symm
      apply Finset.sum_subtype
      intro P
      simp
    _ = ∑ P : MonicIrreducibleLE K n,
          if P.poly.natDegree ∣ n then P.poly.natDegree • f P.poly else 0 := by
      exact Finset.sum_filter _ _

/-! ## The same reindexing for an arbitrary finite extension

This form avoids any dependence on the particular algebra structure chosen
for `FiniteField.Extension`; it is the form used by the rational trace
bridge. -/

section ArbitraryExtension

variable (L : Type*) [Field L] [Finite L] [Algebra K L]
variable [FiniteDimensional K L]

noncomputable local instance : Fintype L := Fintype.ofFinite _

private noncomputable def finiteConjugacyClassClosedPoint
    (hfin : Module.finrank K L = n)
    (c : ConjRootClass K L) : ExtensionClosedPoint K n := by
  let P : K[X] := c.minpoly
  have hdiv : P.natDegree ∣ n := by
    rw [← hfin]
    exact c.irreducible_minpoly.natDegree_dvd_finrank c.splits_minpoly
  exact
    ⟨{ poly := P
       irreducible := c.irreducible_minpoly
       monic := c.monic_minpoly
       natDegree_le := Nat.le_of_dvd (NeZero.pos n) hdiv }, hdiv⟩

private theorem finiteConjugacyClassClosedPoint_injective
    (hfin : Module.finrank K L = n) :
    Function.Injective (finiteConjugacyClassClosedPoint K n L hfin) := by
  intro c d h
  apply ConjRootClass.minpoly_injective
  exact congrArg (fun P : ExtensionClosedPoint K n ↦ P.poly) h

private theorem exists_minpoly_eq_closedPoint_in_finiteExtension
    (hfin : Module.finrank K L = n)
    (P : ExtensionClosedPoint K n) :
    ∃ x : L, minpoly K x = P.poly := by
  letI : Fact (Irreducible P.poly) := ⟨P.irreducible⟩
  have hrootFinrank :
      Module.finrank K (AdjoinRoot P.poly) = P.poly.natDegree := by
    rw [(AdjoinRoot.powerBasis P.irreducible.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim]
  have hdvd : Module.finrank K (AdjoinRoot P.poly) ∣
      Module.finrank K L := by
    rw [hrootFinrank, hfin]
    exact P.natDegree_dvd
  let f : AdjoinRoot P.poly →ₐ[K] L :=
    (FiniteField.nonempty_algHom_of_finrank_dvd hdvd).some
  let x : L := f (AdjoinRoot.root P.poly)
  refine ⟨x, ?_⟩
  have hroot : aeval (AdjoinRoot.root P.poly) P.poly = 0 := by
    rw [Polynomial.aeval_def]
    exact AdjoinRoot.eval₂_root P.poly
  have hminpoly : minpoly K (AdjoinRoot.root P.poly) = P.poly := by
    have h := minpoly.eq_of_irreducible P.irreducible hroot
    simpa [P.monic.leadingCoeff] using h.symm
  calc
    minpoly K x = minpoly K (AdjoinRoot.root P.poly) :=
      minpoly.algHom_eq f f.injective _
    _ = P.poly := hminpoly

private theorem finiteConjugacyClassClosedPoint_surjective
    (hfin : Module.finrank K L = n) :
    Function.Surjective (finiteConjugacyClassClosedPoint K n L hfin) := by
  intro P
  obtain ⟨x, hx⟩ :=
    exists_minpoly_eq_closedPoint_in_finiteExtension K n L hfin P
  refine ⟨ConjRootClass.mk K x, ?_⟩
  apply Subtype.ext
  apply MonicIrreducibleLE.poly_injective
  exact hx

noncomputable def finiteConjugacyClassEquivClosedPoint
    (hfin : Module.finrank K L = n) :
    ConjRootClass K L ≃ ExtensionClosedPoint K n :=
  Equiv.ofBijective (finiteConjugacyClassClosedPoint K n L hfin)
    ⟨finiteConjugacyClassClosedPoint_injective K n L hfin,
      finiteConjugacyClassClosedPoint_surjective K n L hfin⟩

noncomputable local instance : Fintype (ExtensionClosedPoint K n) := by
  unfold ExtensionClosedPoint
  infer_instance

noncomputable local instance
    (c : ConjRootClass K L) : Fintype c.carrier := Fintype.ofFinite _

theorem card_finiteConjugacyClass_carrier
    (c : ConjRootClass K L) :
    Fintype.card c.carrier = c.minpoly.natDegree := by
  calc
    Fintype.card c.carrier = Fintype.card (c.minpoly.rootSet L) :=
      Fintype.card_congr
        (Equiv.setCongr c.rootSet_minpoly_eq_carrier).symm
    _ = c.minpoly.natDegree :=
      Polynomial.card_rootSet_eq_natDegree c.separable_minpoly c.splits_minpoly

theorem sum_finiteExtension_eq_sum_conjugacyClasses
    (hfin : Module.finrank K L = n)
    [Fintype (ConjRootClass K L)]
    {A : Type*} [AddCommMonoid A] (f : K[X] → A) :
    (∑ x : L, f (minpoly K x)) =
      ∑ c : ConjRootClass K L,
        c.minpoly.natDegree • f c.minpoly := by
  classical
  rw [← Fintype.sum_fiberwise (ConjRootClass.mk K)
    (fun x : L ↦ f (minpoly K x))]
  apply Finset.sum_congr rfl
  intro c hc
  calc
    (∑ x : {x : L // ConjRootClass.mk K x = c},
        f (minpoly K x.1)) =
        ∑ _x : {x : L // ConjRootClass.mk K x = c}, f c.minpoly := by
      apply Fintype.sum_congr
      intro x
      rw [← ConjRootClass.minpoly_mk (K := K) x.1, x.2]
    _ = Fintype.card {x : L // ConjRootClass.mk K x = c} •
        f c.minpoly := by
      simp
    _ = Fintype.card c.carrier • f c.minpoly := by
      congr 1
      apply Fintype.card_congr
      exact
        { toFun := fun x ↦ ⟨x.1, x.2⟩
          invFun := fun x ↦ ⟨x.1, x.2⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
    _ = c.minpoly.natDegree • f c.minpoly := by
      rw [card_finiteConjugacyClass_carrier K L c]

theorem sum_finiteExtension_eq_irreducibleSum
    (hfin : Module.finrank K L = n)
    {A : Type*} [AddCommMonoid A] (f : K[X] → A) :
    (∑ x : L, f (minpoly K x)) =
      ∑ P : MonicIrreducibleLE K n,
        if P.poly.natDegree ∣ n then P.poly.natDegree • f P.poly else 0 := by
  classical
  letI : Fintype (ConjRootClass K L) :=
    Fintype.ofEquiv (ExtensionClosedPoint K n)
      (finiteConjugacyClassEquivClosedPoint K n L hfin).symm
  rw [sum_finiteExtension_eq_sum_conjugacyClasses K n L hfin]
  calc
    (∑ c : ConjRootClass K L,
        c.minpoly.natDegree • f c.minpoly) =
        ∑ P : ExtensionClosedPoint K n, P.poly.natDegree • f P.poly := by
      exact (finiteConjugacyClassEquivClosedPoint K n L hfin).sum_comp
        (fun P ↦ P.poly.natDegree • f P.poly)
    _ = ∑ P ∈ (Finset.univ : Finset (MonicIrreducibleLE K n)).filter
          (fun P ↦ P.poly.natDegree ∣ n), P.poly.natDegree • f P.poly := by
      symm
      apply Finset.sum_subtype
      intro P
      simp
    _ = ∑ P : MonicIrreducibleLE K n,
          if P.poly.natDegree ∣ n then P.poly.natDegree • f P.poly else 0 := by
      exact Finset.sum_filter _ _

end ArbitraryExtension

/-! ## Rational-weight specialization over the prime field -/

theorem sum_extension_extensionPointWeight_eq_irreducibleSum
    (p n : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (coeff : ZMod p → ZMod p) :
    (∑ x : FiniteField.Extension (ZMod p) p n,
      extensionPointWeight coeff x) =
      ∑ P : MonicIrreducibleLE (ZMod p) n,
        if P.poly.natDegree ∣ n then
          (P.poly.natDegree : ℂ) *
            polynomialWeight coeff P.poly ^ (n / P.poly.natDegree)
        else 0 := by
  classical
  have hfinrank :
      Module.finrank (ZMod p)
        (FiniteField.Extension (ZMod p) p n) = n := by
    rw [FiniteField.finrank_zmod_extension]
    simp
  have hcore := sum_finiteExtension_eq_irreducibleSum
    (ZMod p) n (FiniteField.Extension (ZMod p) p n) hfinrank
    (fun P : (ZMod p)[X] ↦
      polynomialWeight coeff P ^ (n / P.natDegree))
  calc
    (∑ x : FiniteField.Extension (ZMod p) p n,
        extensionPointWeight coeff x) =
        ∑ x : FiniteField.Extension (ZMod p) p n,
          polynomialWeight coeff (minpoly (ZMod p) x) ^
            (n / (minpoly (ZMod p) x).natDegree) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [extensionPointWeight]
      rw [hfinrank]
    _ = _ := by
      simpa only [nsmul_eq_mul] using hcore

theorem extensionTraceSum_eq_irreducibleSum
    (p n : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (coeff : ZMod p → ZMod p) :
    (∑ x : FiniteField.Extension (ZMod p) p n,
      zeroExtendedTraceWeight coeff x) =
      ∑ P : MonicIrreducibleLE (ZMod p) n,
        if P.poly.natDegree ∣ n then
          (P.poly.natDegree : ℂ) *
            polynomialWeight coeff P.poly ^ (n / P.poly.natDegree)
        else 0 := by
  classical
  calc
    (∑ x : FiniteField.Extension (ZMod p) p n,
        zeroExtendedTraceWeight coeff x) =
        ∑ x : FiniteField.Extension (ZMod p) p n,
          extensionPointWeight coeff x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (extensionPointWeight_eq_zeroExtendedTraceWeight coeff x).symm
    _ = _ := sum_extension_extensionPointWeight_eq_irreducibleSum p n coeff

theorem extensionTraceSum_eq_neg_artinRootPowerSum
    (p n : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty) :
    (∑ x : FiniteField.Extension (ZMod p) p n,
      zeroExtendedTraceWeight coeff x) =
      -((artinLPolynomial coeff).reverse.roots.map
        (fun a ↦ a ^ n)).sum := by
  rw [extensionTraceSum_eq_irreducibleSum p n coeff]
  exact irreducible_sum_eq_neg_artinRootPowerSum
    coeff hne le_rfl (NeZero.ne n)

end RationalWeil

end Erdos387
