import ErdosProblems.Erdos67.StationaryBlockDoubling

/-!
# Splitting prime residues at a dyadic boundary

The equivalences here retain the numerical modulus definitionally, so that
the residue recoding involves no choice of representatives or transport maps.
-/

open MeasureTheory

namespace Erdos67.StationaryModel

open FiniteEntropy

abbrev PrimeBelow (L : ℕ) := {p : Fin L // p.val.Prime}

abbrev PrimeBand (L : ℕ) := {p : Fin (L + L) // p.val.Prime ∧ L ≤ p.val}

def belowModulus (L : ℕ) (p : PrimeBelow L) : ℕ+ := ⟨p.val.val, p.property.pos⟩

def bandModulus (L : ℕ) (p : PrimeBand L) : ℕ+ := ⟨p.val.val, p.property.1.pos⟩

def belowToDouble (L : ℕ) (p : PrimeBelow L) : PrimeBelow (L + L) :=
  ⟨⟨p.val.val, by have := p.val.isLt; omega⟩, p.property⟩

def bandToDouble (L : ℕ) (p : PrimeBand L) : PrimeBelow (L + L) :=
  ⟨p.val, p.property.1⟩

def doubleToBand (L : ℕ) (p : PrimeBelow (L + L)) (hp : L ≤ p.val.val) : PrimeBand L :=
  ⟨p.val, p.property, hp⟩

def doubleToBelow (L : ℕ) (p : PrimeBelow (L + L)) (hp : ¬ L ≤ p.val.val) : PrimeBelow L :=
  ⟨⟨p.val.val, by omega⟩, p.property⟩

/-- All prime residues below `2L` are exactly the fresh and old residue tuples. -/
def splitPrimeResidues (L : ℕ) :
    (∀ p : PrimeBelow (L + L), ZMod (belowModulus (L + L) p).val) ≃
      ((∀ p : PrimeBand L, ZMod (bandModulus L p).val) ×
        (∀ p : PrimeBelow L, ZMod (belowModulus L p).val)) where
  toFun z := (fun p ↦ z (bandToDouble L p), fun p ↦ z (belowToDouble L p))
  invFun z p := if hp : L ≤ p.val.val then z.1 (doubleToBand L p hp)
    else z.2 (doubleToBelow L p hp)
  left_inv z := by
    funext p
    change (if hp : L ≤ p.val.val then z p else z p) = z p
    split <;> rfl
  right_inv z := by
    apply Prod.ext
    · funext p
      change (if hp : L ≤ p.val.val then z.1 p
        else z.2 (doubleToBelow L (bandToDouble L p) hp)) = z.1 p
      exact dif_pos p.property.2
    · funext p
      have hp : ¬ L ≤ (belowToDouble L p).val.val := by
        change ¬ L ≤ p.val.val
        exact Nat.not_le.mpr p.val.isLt
      change (if hp : L ≤ (belowToDouble L p).val.val then
        z.1 (doubleToBand L (belowToDouble L p) hp) else z.2 p) = z.2 p
      exact dif_neg hp

theorem splitPrimeResidues_observable (L : ℕ) :
    splitPrimeResidues L ∘ residueTuple (belowModulus (L + L)) =
      (fun ω ↦ (residueTuple (bandModulus L) ω, residueTuple (belowModulus L) ω)) := rfl

theorem primeBand_below_coprime (L : ℕ) :
    Pairwise (Function.onFun Nat.Coprime
      (fun s : PrimeBand L ⊕ PrimeBelow L ↦
        (Sum.elim (bandModulus L) (belowModulus L) s).val)) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      apply (Nat.coprime_primes a.property.1 b.property.1).2
      intro heq
      exact hab (congrArg Sum.inl (Subtype.ext (Fin.ext heq)))
    | inr b =>
      apply (Nat.coprime_primes a.property.1 b.property).2
      have ha := a.property.2
      have hb := b.val.isLt
      omega
  | inr a =>
    cases b with
    | inl b =>
      apply (Nat.coprime_primes a.property b.property.1).2
      have ha := a.val.isLt
      have hb := b.property.2
      omega
    | inr b =>
      apply (Nat.coprime_primes a.property b.property).2
      intro heq
      exact hab (congrArg Sum.inr (Subtype.ext (Fin.ext heq)))

theorem prime_residue_information_eq (Q : ProbabilityMeasure Configuration) (N L : ℕ) :
    conditionalMutualInfo (signResidueTripleLaw Q (signBlock N)
      (continuous_signBlock N).measurable (bandModulus L) (belowModulus L)) =
        conditionedBlockEntropy Q N (belowModulus L) -
          conditionedBlockEntropy Q N (belowModulus (L + L)) := by
  have hi := conditionalMutualInfo_measureLaw Q (signBlock N)
    (residueTuple (bandModulus L)) (residueTuple (belowModulus L))
    (continuous_signBlock N).measurable (continuous_residueTuple _).measurable
    (continuous_residueTuple _).measurable
  have he := condEntropyOf_equiv Q (signBlock N) (residueTuple (belowModulus (L + L)))
    (continuous_signBlock N).measurable (continuous_residueTuple _).measurable
    (Equiv.refl _) (splitPrimeResidues L)
  have hc := condEntropyOf_congr Q (signBlock N) (signBlock N) _ _
    (continuous_signBlock N).measurable (continuous_signBlock N).measurable
    ((measurable_of_countable (splitPrimeResidues L)).comp
      (continuous_residueTuple _).measurable)
    ((continuous_residueTuple _).measurable.prodMk (continuous_residueTuple _).measurable)
    rfl (splitPrimeResidues_observable L)
  change _ = conditionedBlockEntropy Q N (belowModulus L) - _ at hi
  exact hi.trans (congrArg (fun t ↦ conditionedBlockEntropy Q N (belowModulus L) - t)
    (hc.symm.trans he))

end Erdos67.StationaryModel
