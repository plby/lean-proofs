import ErdosProblems.Erdos157b.LocalEncoding

/-! Ordered enumerations of unordered prime triples, and their logarithmic products. -/

namespace Erdos157.Binary

open Erdos157.Elementary

open Polynomial PolynomialCharacters AuxiliaryModuli

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

noncomputable def primeTripleEquiv {k : ℕ} (T : PrimeTriple K (levelDegree k)) : Fin 3 ≃ T.1 :=
  (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using T.2)).symm

noncomputable def primeTripleEntry {k : ℕ} (T : PrimeTriple K (levelDegree k)) (j : Fin 3) :
    LevelLabel K k := (primeTripleEquiv K T j).val

theorem primeTripleEntry_mem {k : ℕ} (T : PrimeTriple K (levelDegree k)) (j : Fin 3) :
    primeTripleEntry K T j ∈ T.1 := (primeTripleEquiv K T j).property

theorem primeTripleEntry_injective {k : ℕ} (T : PrimeTriple K (levelDegree k)) :
    Function.Injective (primeTripleEntry K T) :=
  Subtype.val_injective.comp (primeTripleEquiv K T).injective

theorem primeTripleEntry_prod {k : ℕ} (T : PrimeTriple K (levelDegree k))
    {G : Type*} [CommMonoid G] (f : LevelLabel K k → G) :
    (∏ j : Fin 3, f (primeTripleEntry K T j)) = ∏ a ∈ T.1, f a := by
  have he := Fintype.prod_equiv (primeTripleEquiv K T)
    (fun j => f (primeTripleEntry K T j)) (fun a => f a.1) (fun _ => rfl)
  simpa only [Finset.prod_coe_sort] using he

theorem primeAtLevelResidue_val (k : ℕ) (f : LevelLabel K k) (i : ℕ) :
    (primeAtLevelResidue K k f i).val = AdjoinRoot.mk (factor K i) f.1.1 := IsUnit.unit_spec _

theorem levelTripleResidue_coordinate (k : ℕ) (T : PrimeTriple K (levelDegree k)) (i : Fin k) :
    quotientUnitsEquiv K k (levelTripleResidue k k T) i =
      ∏ a ∈ T.1, primeAtLevelResidue K k a i := by
  apply Units.ext
  rw [quotientUnitsEquiv_val_apply]
  simp only [levelTripleResidue, PrimeTriple.residueUnit_val, quotientEquiv_mk_apply,
    PrimeTriple.product, primeSetProduct, map_prod, Units.coe_prod, primeAtLevelResidue_val]
  simp only [Finset.prod_apply, quotientEquiv_mk_apply]

theorem levelTripleResidue_log (k : ℕ) (T : PrimeTriple K (levelDegree k)) (i : Fin k) :
    unitLogEquiv K k (levelTripleResidue k k T) i =
      CyclicLog.log (primeAtLevelResidue K k (primeTripleEntry K T 0) i) +
        CyclicLog.log (primeAtLevelResidue K k (primeTripleEntry K T 1) i) +
        CyclicLog.log (primeAtLevelResidue K k (primeTripleEntry K T 2) i) := by
  change CyclicLog.log (quotientUnitsEquiv K k (levelTripleResidue k k T) i) = _
  rw [levelTripleResidue_coordinate, ← primeTripleEntry_prod K T,
    Fin.prod_univ_three, CyclicLog.log_mul, CyclicLog.log_mul]

end Erdos157.Binary
