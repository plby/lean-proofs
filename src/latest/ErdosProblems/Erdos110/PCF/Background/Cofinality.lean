import Mathlib.SetTheory.Cardinal.Cofinality
import ErdosProblems.Erdos110.PCF.Background.Ordinal

/-!
Adapted from Y. Paz, `PCF-Theory` (Apache 2.0), and ported to Mathlib v4.33.0.
-/

universe u v

open Cardinal Set

namespace Ordinal

-- #14060
/-- A version of `iSup_lt_ord_lift` with more general universes -/
theorem iSup_lt_ord_lift' {ι : Type v} {f : ι → Ordinal.{u}} {c : Ordinal.{u}}
    (hι : Cardinal.lift.{u} #ι < Cardinal.lift.{v} c.cof) : (∀ i, f i < c) → iSup f < c := by
  have : Small.{u, u + 1} ↑(range f) := by
    have : Small.{u, v} ι := by
      let g : ι ↪ c.cof.out := by
        have e1 : ι ↪ (Cardinal.lift.{u} #ι).out :=
          ((Classical.choice (out_lift_equiv.{v, u} #ι)).trans outMkEquiv).symm.toEmbedding
        refine e1.trans ?_
        have e2 : (Cardinal.lift.{u} #ι).out ↪ (Cardinal.lift.{v, u} c.cof).out := by
          refine Classical.choice <| (Cardinal.le_def _ _).mp ?_
          rw [mk_out, mk_out, lift_cof, ← lift_cof]
          exact hι.le
        exact e2.trans <| Equiv.toEmbedding <| Classical.choice <| out_lift_equiv.{u, v} c.cof
      exact small_of_injective g.injective
    exact small_range _
  intro h
  let g : ι → Ordinal.{max u v} := fun x ↦ lift (f x)
  have : iSup g < lift.{v} c := by
    apply iSup_lt_ord_lift
    · exact (lift_cof _) ▸ hι
    · exact fun i ↦ lift_lt.mpr (h i)
  have aux : iSup g = lift.{v} (iSup f) := by
    refine Eq.symm (lift_iSup bddAbove_of_small)
  rw [aux] at this
  convert this
  simp_all only [lift_cof, lift_lt, g]

theorem iSup_Iio_lt_ord {δ : Ordinal.{u}} {ℓ : Ordinal.{v}} {f : Iio ℓ → Ordinal.{u}}
    (hf : ∀ i, f i < δ) (hcard : Cardinal.lift.{u} ℓ.card < Cardinal.lift.{v} δ.cof) :
    iSup f < δ := by
  refine iSup_lt_ord_lift' ?_ hf
  · rw [mk_Iio_ordinal, Cardinal.lift_lift]
    have aux1 : Cardinal.lift.{max (v + 1) u, v} ℓ.card =
      Cardinal.lift.{v + 1} (Cardinal.lift.{u, v} ℓ.card) := (Cardinal.lift_lift _).symm
    have aux2 : Cardinal.lift.{v + 1, u} δ.cof =
      Cardinal.lift.{v + 1} (Cardinal.lift.{v, u} δ.cof) := (Cardinal.lift_lift _).symm
    rwa [aux1, aux2, Cardinal.lift_lt]
