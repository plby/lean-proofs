import ErdosProblems.Erdos67.StationaryResidues
import ErdosProblems.Erdos67.StationaryConditionalEntropy

/-!
# Independence of disjoint coprime residue families

The independence statement used by the conditional entropy estimate is derived
from the uniform CRT law, including its formulation inside a joint sign/residue
probability vector.
-/

open scoped BigOperators
open MeasureTheory

namespace Erdos67.FiniteEntropy

variable {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]

theorem map_uniformVector (e : A ≃ B) :
    stdSimplex.map e (uniformVector (α := A)) = uniformVector (α := B) := by
  apply Subtype.ext
  funext b
  obtain ⟨a, rfl⟩ := e.surjective b
  change stdSimplex.map e uniformVector (e a) = uniformVector (e a)
  rw [map_equiv_apply, uniformVector_apply, uniformVector_apply, Fintype.card_congr e]

theorem product_uniformVector :
    product (uniformVector (α := A)) (uniformVector (α := B)) =
      uniformVector (α := A × B) := by
  apply Subtype.ext
  funext z
  change (Fintype.card A : ℝ)⁻¹ * (Fintype.card B : ℝ)⁻¹ =
    (Fintype.card (A × B) : ℝ)⁻¹
  simp only [Fintype.card_prod, Nat.cast_mul, mul_inv_rev, mul_comm]

end Erdos67.FiniteEntropy

namespace Erdos67.StationaryModel

open FiniteEntropy

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem residueTuple_pair_law_product (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (p : ι → ℕ+) (q : κ → ℕ+)
    (hcoprime : Pairwise (Function.onFun Nat.Coprime
      (fun s : ι ⊕ κ ↦ (Sum.elim p q s).val))) :
    measureLaw Q (fun ω ↦ (residueTuple p ω, residueTuple q ω))
      ((continuous_residueTuple p).measurable.prodMk (continuous_residueTuple q).measurable) =
        product uniformVector uniformVector := by
  let e := Equiv.sumPiEquivProdPi (fun s : ι ⊕ κ ↦ ZMod (Sum.elim p q s).val)
  have hu := residueTuple_law_uniform Q hQ (Sum.elim p q) hcoprime
  have hm := measureLaw_map Q (residueTuple (Sum.elim p q))
    (continuous_residueTuple _).measurable e (measurable_of_countable e)
  rw [hu, map_uniformVector] at hm
  rw [product_uniformVector]
  exact hm

/-- Joint law with a sign block, a fresh residue family, and older residues. -/
noncomputable def signResidueTripleLaw {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (Q : ProbabilityMeasure Configuration)
    (X : Configuration → A) (hX : Measurable X) (p : ι → ℕ+) (q : κ → ℕ+) :
    FinProb ((A × (∀ i, ZMod (p i).val)) × (∀ j, ZMod (q j).val)) :=
  measureLaw Q (fun ω ↦ ((X ω, residueTuple p ω), residueTuple q ω))
    ((hX.prodMk (continuous_residueTuple p).measurable).prodMk
      (continuous_residueTuple q).measurable)

theorem signResidueTripleLaw_residue_marginal {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (Q : ProbabilityMeasure Configuration)
    (X : Configuration → A) (hX : Measurable X) (p : ι → ℕ+) (q : κ → ℕ+) :
    mapLeft (signResidueTripleLaw Q X hX p q) Prod.snd =
      measureLaw Q (fun ω ↦ (residueTuple p ω, residueTuple q ω))
        ((continuous_residueTuple p).measurable.prodMk (continuous_residueTuple q).measurable) := by
  exact (measureLaw_map Q
    (fun ω ↦ ((X ω, residueTuple p ω), residueTuple q ω))
    ((hX.prodMk (continuous_residueTuple p).measurable).prodMk
      (continuous_residueTuple q).measurable)
    (fun z ↦ (z.1.2, z.2)) ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).symm

/-- The independence premise of the finite entropy estimate follows from
stationarity and coprimality; no independence of the sign block is asserted. -/
theorem signResidueTripleLaw_independent_residues {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (X : Configuration → A) (hX : Measurable X) (p : ι → ℕ+) (q : κ → ℕ+)
    (hcoprime : Pairwise (Function.onFun Nat.Coprime
      (fun s : ι ⊕ κ ↦ (Sum.elim p q s).val))) :
    mapLeft (signResidueTripleLaw Q X hX p q) Prod.snd =
      product uniformVector (sndMarginal (signResidueTripleLaw Q X hX p q)) := by
  have hpair := signResidueTripleLaw_residue_marginal Q X hX p q
  rw [residueTuple_pair_law_product Q hQ p q hcoprime] at hpair
  have hmarg := congrArg sndMarginal hpair
  rw [sndMarginal_mapLeft, sndMarginal_product] at hmarg
  rw [hmarg]
  exact hpair

end Erdos67.StationaryModel
