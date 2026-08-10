import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos206

set_option linter.style.setOption false
set_option linter.flexible false

open scoped BigOperators ENNReal
open Finset MeasureTheory Set

namespace EgyptianFractions

noncomputable def egyptianSum (S : Finset ℕ) : ℝ :=
  S.sum (fun m => (1 : ℝ) / m)

def ValidEgyptian (S : Finset ℕ) : Prop :=
  ∀ m ∈ S, 0 < m

def IsUnderapprox (S : Finset ℕ) (x : ℝ) : Prop :=
  ValidEgyptian S ∧ egyptianSum S < x

def IsBestNTerm (S : Finset ℕ) (n : ℕ) (x : ℝ) : Prop :=
  S.card = n ∧ IsUnderapprox S x ∧
    ∀ T : Finset ℕ, T.card = n → IsUnderapprox T x → egyptianSum T ≤ egyptianSum S

def EventuallyGreedy (x : ℝ) : Prop :=
  x > 0 ∧ ∃ (m : ℕ → ℕ), StrictMono m ∧ (∀ k, 0 < m k) ∧
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      IsBestNTerm (Finset.image m (Finset.range n)) n x
end EgyptianFractions

end Erdos206

attribute [local instance] Classical.propDecidable

theorem Erdos206.EgyptianFractions.erdos_206 :
    @Eq.{1} ENNReal
      (@DFunLike.coe.{1, 1, 1}
        (@MeasureTheory.Measure.{0} Real
          (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace))
        (Set.{0} Real) (fun (x : Set.{0} Real) ↦ ENNReal)
        (@MeasureTheory.Measure.instFunLike.{0} Real
          (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace))
        (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)
        (@setOf.{0} Real fun (x : Real) ↦ Erdos206.EgyptianFractions.EventuallyGreedy x))
      (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))
  := by
  sorry
