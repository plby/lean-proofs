import ErdosProblems.Erdos157.PrefixTripleSupply
import Mathlib.GroupTheory.Coset.Basic

/-! Uniform extension of a unit residue from a prefix modulus. -/

namespace Erdos157.Elementary.AuxiliaryModuli

open Polynomial PolynomialCharacters FiniteFiberCounts

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

noncomputable instance quotientFinite (k : ℕ) : Finite (AdjoinRoot (product K k)) :=
  Finite.of_injective (quotientEquiv K k) (quotientEquiv K k).injective

noncomputable instance quotientUnitsFintype (k : ℕ) : Fintype (AdjoinRoot (product K k))ˣ :=
  Fintype.ofFinite _

noncomputable def prefixVectorMap {h k : ℕ} (hhk : h ≤ k) :
    (∀ i : Fin k, (ResidueField K i)ˣ) →* (∀ i : Fin h, (ResidueField K i)ˣ) where
  toFun v i := v ⟨i.1, lt_of_lt_of_le i.2 hhk⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem prefixVectorMap_surjective {h k : ℕ} (hhk : h ≤ k) :
    Function.Surjective (prefixVectorMap K hhk) := by
  intro v
  refine ⟨fun j => if hj : j.1 < h then v ⟨j.1, hj⟩ else 1, ?_⟩
  ext i
  simp only [prefixVectorMap, MonoidHom.coe_mk, OneHom.coe_mk, dif_pos i.2]

noncomputable def quotientProjection {h k : ℕ} (hhk : h ≤ k) :
    (AdjoinRoot (product K k))ˣ →* (AdjoinRoot (product K h))ˣ :=
  (quotientUnitsEquiv K h).symm.toMonoidHom.comp
    ((prefixVectorMap K hhk).comp (quotientUnitsEquiv K k).toMonoidHom)

theorem quotientProjection_coordinates {h k : ℕ} (hhk : h ≤ k)
    (u : (AdjoinRoot (product K k))ˣ) :
    quotientUnitsEquiv K h (quotientProjection K hhk u) =
      prefixVectorMap K hhk (quotientUnitsEquiv K k u) :=
  (quotientUnitsEquiv K h).apply_symm_apply _

theorem quotientProjection_surjective {h k : ℕ} (hhk : h ≤ k) :
    Function.Surjective (quotientProjection K hhk) := by
  intro u
  obtain ⟨v, hv⟩ := prefixVectorMap_surjective K hhk (quotientUnitsEquiv K h u)
  refine ⟨(quotientUnitsEquiv K k).symm v, ?_⟩
  apply (quotientUnitsEquiv K h).injective
  rw [quotientProjection_coordinates, MulEquiv.apply_symm_apply, hv]

theorem quotientProjection_levelTripleResidue (l : ℕ) {h k : ℕ} (hhk : h ≤ k)
    (T : PrimeTriple K (levelDegree l)) :
    quotientProjection K hhk (levelTripleResidue l k T) = levelTripleResidue l h T := by
  apply (quotientUnitsEquiv K h).injective
  rw [quotientProjection_coordinates]
  ext i
  change (↑(quotientUnitsEquiv K k (levelTripleResidue l k T)
      ⟨i.1, lt_of_lt_of_le i.2 hhk⟩) : ResidueField K i) =
        ↑(quotientUnitsEquiv K h (levelTripleResidue l h T) i)
  rw [quotientUnitsEquiv_val_apply, quotientUnitsEquiv_val_apply]
  simp only [levelTripleResidue, PrimeTriple.residueUnit_val, quotientEquiv_mk_apply]

/-- Every prefix class has the same number of full unit-residue extensions. -/
theorem quotientProjection_fiberCard_mul {h k : ℕ} (hhk : h ≤ k)
    (u : (AdjoinRoot (product K h))ˣ) :
    fiberCard (quotientProjection K hhk) u * Nat.card (AdjoinRoot (product K h))ˣ =
      Nat.card (AdjoinRoot (product K k))ˣ := by
  have heq (v : (AdjoinRoot (product K h))ˣ) :
      fiberCard (quotientProjection K hhk) v = fiberCard (quotientProjection K hhk) u :=
    Nat.card_congr (MonoidHom.fiberEquivOfSurjective (quotientProjection_surjective K hhk) v u)
  have hs := sum_fiberCard (quotientProjection K hhk)
  simp only [heq, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hs
  simpa only [Nat.card_eq_fintype_card, mul_comm] using hs

end Erdos157.Elementary.AuxiliaryModuli
