/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.ZMod.QuotientRing

/-!
# Coordinatewise counting through the Chinese remainder equivalence

This file records the elementary finite-product count used in the
Pollington--Vaughan pair estimate.  If the moduli are pairwise coprime, the
Chinese remainder equivalence identifies a residue modulo their product with
one residue at every local modulus.  Consequently, a coordinatewise family of
allowed sets has cardinality equal to the product of its local cardinalities.
-/

open scoped BigOperators

namespace Erdos999

noncomputable section

private local instance productNeZero
    {ι : Type*} [Fintype ι] (a : ι → ℕ) [(i : ι) → NeZero (a i)] :
    NeZero (∏ i, a i) where
  out := Finset.prod_ne_zero_iff.mpr fun i _ => NeZero.ne (a i)

/-- A coordinatewise allowed set in a product of pairwise-coprime residue
rings has the product of the local cardinalities. -/
theorem card_filter_crt_allowed
    {ι : Type*} [Fintype ι]
    (a : ι → ℕ) [(i : ι) → NeZero (a i)]
    (hcoprime : Pairwise (Function.onFun Nat.Coprime a))
    (allowed : (i : ι) → Finset (ZMod (a i))) :
    ((Finset.univ : Finset (ZMod (∏ i, a i))).filter
      (fun z => ∀ i, ZMod.prodEquivPi a hcoprime z i ∈ allowed i)).card =
      ∏ i, (allowed i).card := by
  classical
  let e := (ZMod.prodEquivPi a hcoprime).toEquiv
  let E :
      {z : ZMod (∏ i, a i) // ∀ i, e z i ∈ allowed i} ≃
        ((i : ι) → (allowed i : Type)) :=
    { toFun := fun z i => ⟨e z.1 i, z.2 i⟩
      invFun := fun x => ⟨e.symm (fun i => (x i : ZMod (a i))), by
        intro i
        rw [e.apply_symm_apply]
        exact (x i).property⟩
      left_inv := by
        intro z
        apply Subtype.ext
        exact e.symm_apply_apply z.1
      right_inv := by
        intro x
        funext i
        apply Subtype.ext
        exact congr_fun (e.apply_symm_apply (fun i => (x i : ZMod (a i)))) i }
  rw [← Fintype.card_subtype
    (fun z : ZMod (∏ i, a i) =>
      ∀ i, ZMod.prodEquivPi a hcoprime z i ∈ allowed i)]
  change Fintype.card {z : ZMod (∏ i, a i) // ∀ i, e z i ∈ allowed i} = _
  rw [Fintype.card_congr E, Fintype.card_pi]
  simp only [Fintype.card_coe]

/-- Complement form of `card_filter_crt_allowed`: the number of residues
avoiding a prescribed finite forbidden set in every coordinate is the product
of the numbers of locally allowed residues. -/
theorem card_filter_crt_avoiding
    {ι : Type*} [Fintype ι]
    (a : ι → ℕ) [(i : ι) → NeZero (a i)]
    (hcoprime : Pairwise (Function.onFun Nat.Coprime a))
    (forbidden : (i : ι) → Finset (ZMod (a i))) :
    ((Finset.univ : Finset (ZMod (∏ i, a i))).filter
      (fun z => ∀ i, ZMod.prodEquivPi a hcoprime z i ∉ forbidden i)).card =
      ∏ i, (a i - (forbidden i).card) := by
  classical
  let allowed : (i : ι) → Finset (ZMod (a i)) :=
    fun i => Finset.univ \ forbidden i
  simpa only [allowed, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, ZMod.card] using
    (card_filter_crt_allowed a hcoprime allowed)

/-- Distinct members of a finite set of primes are pairwise coprime. -/
theorem primeFinset_pairwiseCoprime
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Pairwise (Function.onFun Nat.Coprime (fun p : P => (p : ℕ))) := by
  intro p q hpq
  apply (Nat.coprime_primes (hP p p.property) (hP q q.property)).2
  intro hpqval
  exact hpq (Subtype.ext hpqval)

/-- Prime-indexed specialization of `card_filter_crt_avoiding`. -/
theorem card_filter_primeCRT_avoiding
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    [(p : P) → NeZero (p : ℕ)]
    (forbidden : (p : P) → Finset (ZMod (p : ℕ))) :
    ((Finset.univ : Finset (ZMod (∏ p : P, (p : ℕ)))).filter
      (fun z => ∀ p : P,
        ZMod.prodEquivPi (fun p : P => (p : ℕ))
          (primeFinset_pairwiseCoprime P hP) z p ∉ forbidden p)).card =
      ∏ p : P, ((p : ℕ) - (forbidden p).card) := by
  exact card_filter_crt_avoiding (fun p : P => (p : ℕ))
    (primeFinset_pairwiseCoprime P hP) forbidden

end

end Erdos999
