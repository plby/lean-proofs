import Util.Bernays.SplitPrimeClasses
import Mathlib.Data.ZMod.QuotientGroup

/-!
# Exact local and simultaneous sieve densities at split primes
-/

open scoped Classical

namespace Bernays

def affineScalarEquiv {K : Type*} [Field K] (c μ : K) (hμ : μ ≠ 0) : K ≃ K where
  toFun x := c + μ * x
  invFun y := (y - c) / μ
  left_inv x := by field_simp; ring
  right_inv y := by field_simp; ring

def rootCoordinateEquiv {K : Type*} [Field K] (r s : K) (hrs : r ≠ s) : K × K ≃ K × K where
  toFun x := (x.1 + x.2 * r, x.1 + x.2 * s)
  invFun y := ((r * y.2 - s * y.1) / (r - s), (y.1 - y.2) / (r - s))
  left_inv x := by
    have h : r - s ≠ 0 := sub_ne_zero.mpr hrs
    apply Prod.ext <;> dsimp only <;> field_simp <;> ring
  right_inv y := by
    have h : r - s ≠ 0 := sub_ne_zero.mpr hrs
    apply Prod.ext <;> dsimp only <;> field_simp <;> ring

def AffineAllowedPairs {K : Type*} [Field K] (r s c₀ c₁ μ : K) :=
  {x : K × K // c₀ + μ * x.1 + (c₁ + μ * x.2) * r ≠ 0 ∧
    c₀ + μ * x.1 + (c₁ + μ * x.2) * s ≠ 0}

def affineAllowedPairsEquiv {K : Type*} [Field K] (r s c₀ c₁ μ : K)
    (hrs : r ≠ s) (hμ : μ ≠ 0) :
    AffineAllowedPairs r s c₀ c₁ μ ≃ {x : K // x ≠ 0} × {y : K // y ≠ 0} :=
  (Equiv.subtypeEquiv
    ((Equiv.prodCongr (affineScalarEquiv c₀ μ hμ) (affineScalarEquiv c₁ μ hμ)).trans
      (rootCoordinateEquiv r s hrs)) (fun _ => Iff.rfl)).trans
    { toFun := fun (x : {x : K × K // x.1 ≠ 0 ∧ x.2 ≠ 0}) =>
        (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
      invFun := fun (x : {x : K // x ≠ 0} × {y : K // y ≠ 0}) =>
        ⟨(x.1.1, x.2.1), x.1.2, x.2.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }

theorem natCard_affineAllowedPairs {q : ℕ} [Fact q.Prime] (r s c₀ c₁ μ : ZMod q)
    (hrs : r ≠ s) (hμ : μ ≠ 0) :
    Nat.card (AffineAllowedPairs r s c₀ c₁ μ) = (q - 1) ^ 2 := by
  have hcard : Nat.card {x : ZMod q // x ≠ 0} = q - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp
  rw [Nat.card_congr (affineAllowedPairsEquiv r s c₀ c₁ μ hrs hμ), Nat.card_prod, hcard, pow_two]

variable {d b : ℤ}

def splitSieveModulus (S : Finset (SplitPrime d b)) : ℕ := ∏ s ∈ S, s.1

theorem splitSieveModulus_pos (S : Finset (SplitPrime d b)) : 0 < splitSieveModulus S :=
  Finset.prod_pos fun s _ => s.2.1.pos

theorem splitPrime_pairwise_coprime (S : Finset (SplitPrime d b)) :
    Pairwise (fun a b : {s // s ∈ S} => Nat.Coprime a.1.1 b.1.1) := by
  intro a b hab
  apply (Nat.coprime_primes a.1.2.1 b.1.2.1).mpr
  intro hq
  exact hab (Subtype.ext (Subtype.ext hq))

noncomputable def splitResidueEquivPi (S : Finset (SplitPrime d b)) :
    ZMod (splitSieveModulus S) ≃+* (∀ s : {s // s ∈ S}, ZMod s.1.1) := by
  have hprod : (∏ s : {s // s ∈ S}, s.1.1) = splitSieveModulus S := by
    simpa only [Finset.attach_eq_univ, splitSieveModulus] using S.prod_attach (fun s => s.1)
  exact (ZMod.ringEquivCongr hprod.symm).trans
    (ZMod.prodEquivPi (fun s : {s // s ∈ S} => s.1.1) (splitPrime_pairwise_coprime S))

theorem splitResidueEquivPi_apply (S : Finset (SplitPrime d b))
    (x : ZMod (splitSieveModulus S)) (s : {s // s ∈ S}) :
    splitResidueEquivPi S x s = (x.val : ZMod s.1.1) := by
  letI : NeZero (splitSieveModulus S) := ⟨(splitSieveModulus_pos S).ne'⟩
  have hdiv : s.1.1 ∣ splitSieveModulus S := Finset.dvd_prod_of_mem (fun s => s.1) s.2
  let f : ZMod (splitSieveModulus S) →+* ZMod s.1.1 :=
    (Pi.evalRingHom (fun s : {s // s ∈ S} => ZMod s.1.1) s).comp (splitResidueEquivPi S).toRingHom
  have hf : f = ZMod.castHom hdiv (ZMod s.1.1) := Subsingleton.elim _ _
  change f x = _
  rw [hf, ZMod.castHom_apply, ZMod.cast_eq_val]

noncomputable def splitResiduePairEquivPi (S : Finset (SplitPrime d b)) :
    (ZMod (splitSieveModulus S) × ZMod (splitSieveModulus S)) ≃
      (∀ s : {s // s ∈ S}, ZMod s.1.1 × ZMod s.1.1) := by
  let e := splitResidueEquivPi S
  exact
    { toFun x s := (e x.1 s, e x.2 s)
      invFun y := (e.symm (fun s => (y s).1), e.symm (fun s => (y s).2))
      left_inv x := Prod.ext (e.symm_apply_apply x.1) (e.symm_apply_apply x.2)
      right_inv y := by
        funext s
        exact Prod.ext (congrFun (e.apply_symm_apply (fun s => (y s).1)) s)
          (congrFun (e.apply_symm_apply (fun s => (y s).2)) s) }

theorem splitResiduePairEquivPi_apply (S : Finset (SplitPrime d b))
    (x : ZMod (splitSieveModulus S) × ZMod (splitSieveModulus S)) (s : {s // s ∈ S}) :
    splitResiduePairEquivPi S x s = ((x.1.val : ZMod s.1.1), (x.2.val : ZMod s.1.1)) := by
  apply Prod.ext <;> exact splitResidueEquivPi_apply S _ s

def AffineAllowedResiduePairs (S : Finset (SplitPrime d b))
    (c : QuadraticAlgebra ℤ d b) (μ : ℤ) :=
  {x : ZMod (splitSieveModulus S) × ZMod (splitSieveModulus S) // ∀ s : {s // s ∈ S},
    (c.re : ZMod s.1.1) + (μ : ZMod s.1.1) * (splitResiduePairEquivPi S x s).1 +
      ((c.im : ZMod s.1.1) + (μ : ZMod s.1.1) * (splitResiduePairEquivPi S x s).2) * s.1.root ≠ 0 ∧
    (c.re : ZMod s.1.1) + (μ : ZMod s.1.1) * (splitResiduePairEquivPi S x s).1 +
      ((c.im : ZMod s.1.1) + (μ : ZMod s.1.1) * (splitResiduePairEquivPi S x s).2) *
        ((b : ZMod s.1.1) - s.1.root) ≠ 0}

noncomputable def affineAllowedResiduePairsEquivPi (S : Finset (SplitPrime d b))
    (c : QuadraticAlgebra ℤ d b) (μ : ℤ) :
    AffineAllowedResiduePairs S c μ ≃
      (∀ s : {s // s ∈ S}, AffineAllowedPairs s.1.root ((b : ZMod s.1.1) - s.1.root)
        (c.re : ZMod s.1.1) (c.im : ZMod s.1.1) (μ : ZMod s.1.1)) := by
  let e := splitResiduePairEquivPi S
  exact
    { toFun x s := ⟨e x.1 s, x.2 s⟩
      invFun y := ⟨e.symm (fun s => (y s).1), by
        intro s
        simpa only [e, Equiv.apply_symm_apply] using (y s).2⟩
      left_inv x := Subtype.ext (e.symm_apply_apply x.1)
      right_inv y := by
        funext s
        exact Subtype.ext (congrFun (e.apply_symm_apply (fun s => (y s).1)) s) }

theorem natCard_affineAllowedResiduePairs (S : Finset (SplitPrime d b))
    (c : QuadraticAlgebra ℤ d b) (μ : ℤ) (hμ : ∀ s ∈ S, (μ : ZMod s.1) ≠ 0) :
    Nat.card (AffineAllowedResiduePairs S c μ) = ∏ s ∈ S, (s.1 - 1) ^ 2 := by
  rw [Nat.card_congr (affineAllowedResiduePairsEquivPi S c μ), Nat.card_pi]
  have hlocal (s : {s // s ∈ S}) : Nat.card
      (AffineAllowedPairs s.1.root ((b : ZMod s.1.1) - s.1.root)
        (c.re : ZMod s.1.1) (c.im : ZMod s.1.1) (μ : ZMod s.1.1)) = (s.1.1 - 1) ^ 2 :=
    natCard_affineAllowedPairs _ _ _ _ _
      (quadratic_roots_distinct _ _ _ s.1.root_sq s.1.discr_ne_zero) (hμ s.1 s.2)
  simp_rw [hlocal]
  simpa only [Finset.attach_eq_univ] using S.prod_attach (fun s => (s.1 - 1) ^ 2)

end Bernays
