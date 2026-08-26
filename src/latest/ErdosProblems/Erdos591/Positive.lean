import ErdosProblems.Erdos591.GlobalIndiv
import ErdosProblems.Erdos591.LocalAssembly

open Cardinal Ordinal

namespace Erdos591.Positive

open Erdos591.Schipperus
open GlobalIndiv

/-!
These are ordinal-arithmetic and finite-indivisibility inputs at
`lambda = omega^(omega^2)`, not an endpoint partition proof.  For block
indices of type `lambda` and reservoirs of type `omega^omega`, the relevant
lexicographic sums have type `lambda`:

* `omega^omega * lambda = lambda`;
* `omega * lambda = lambda`.

Finite unary indivisibility at `lambda` is supplied by `GlobalIndiv`.
The missing global combinatorial argument is discussed at the end.
-/

theorem exponent_bounded_of_lt_omega_sq {e : Ordinal.{0}}
    (he : e < ω ^ 2) : ∃ k : ℕ, e ≤ ω * (k : Ordinal.{0}) := by
  rw [pow_two] at he
  obtain ⟨q, hq, r, hr, her⟩ := Ordinal.lt_mul_iff.mp he
  obtain ⟨q, rfl⟩ := Ordinal.lt_omega0.mp hq
  refine ⟨q + 1, ?_⟩
  rw [her]
  have hlt : ω * (q : Ordinal.{0}) + r <
      ω * (q : Ordinal.{0}) + ω :=
    (add_lt_add_iff_left _).2 hr
  apply hlt.le.trans_eq
  norm_num [Nat.cast_add, mul_add]

/-- Every omega-power whose exponent is at most `omega^2` is finitely
indivisible.  Strictly below the endpoint this is the finite CNF argument;
at the endpoint it is the nested-list diagonal theorem. -/
theorem omegaPower_finitelyIndivisible_of_le_omega_sq
    (h590 : OrdinalCardinalRamsey
      (ω ^ ω : Ordinal.{0}) (ω ^ ω : Ordinal.{0}) 3)
    {P : Type} [LinearOrder P] [WellFoundedLT P]
    (e : Ordinal.{0}) (hP : typeLT P = ω ^ e) (he : e ≤ ω ^ 2) :
    K4Core.FinitelyIndivisible P := by
  rcases he.eq_or_lt with heq | hlt
  · have htype : typeLT lambda.ToType = typeLT P := by
      rw [Ordinal.type_toType, hP, heq]
    let iso :
        ((· < ·) : lambda.ToType → lambda.ToType → Prop) ≃r
          ((· < ·) : P → P → Prop) :=
      Classical.choice (Ordinal.type_eq.mp htype)
    exact PieceIndiv.k4_of_relFiniteIndivisible
      (lambda_relFiniteIndivisible.congr iso)
  · obtain ⟨k, hk⟩ := exponent_bounded_of_lt_omega_sq hlt
    exact PieceIndiv.omegaPower_finitelyIndivisible_of_le
      h590 e k hP hk

theorem omega_add_omega_sq :
    (ω : Ordinal.{0}) + ω ^ 2 = ω ^ 2 := by
  rw [← Ordinal.opow_natCast]
  apply Ordinal.add_omega0_opow
  simpa only [Ordinal.opow_one] using
    (Ordinal.opow_lt_opow_iff_right
      (a := (ω : Ordinal.{0})) (b := (1 : Ordinal.{0}))
      (c := ((2 : ℕ) : Ordinal.{0})) Ordinal.one_lt_omega0).2 (by
      norm_num)

theorem omegaOmega_mul_lambda :
    (ω ^ ω : Ordinal.{0}) * lambda = lambda := by
  rw [← Ordinal.opow_add, omega_add_omega_sq]

theorem omega_mul_lambda : (ω : Ordinal.{0}) * lambda = lambda := by
  have hω : (ω : Ordinal.{0}) ≤ (ω : Ordinal.{0}) ^ (2 : ℕ) := by
    rw [← Ordinal.opow_natCast]
    simpa only [Ordinal.opow_one] using Ordinal.opow_le_opow_right
      (a := (ω : Ordinal.{0})) (b := (1 : Ordinal.{0}))
      (c := ((2 : ℕ) : Ordinal.{0})) Ordinal.omega0_pos (by norm_num)
  calc
    (ω : Ordinal.{0}) * lambda = ω ^ ((1 : Ordinal.{0}) + ω ^ 2) := by
      rw [Ordinal.opow_one_add]
    _ = lambda := by
      change (ω : Ordinal.{0}) ^ ((1 : Ordinal.{0}) + ω ^ 2) =
        (ω : Ordinal.{0}) ^ (ω ^ 2)
      exact congrArg (fun e : Ordinal.{0} ↦ (ω : Ordinal.{0}) ^ e)
        (Ordinal.one_add_of_omega0_le hω)

abbrev Inner : Type := (ω ^ ω : Ordinal.{0}).ToType
abbrev Index : Type := lambda.ToType

/-- `lambda` many consecutive `omega^omega` reservoirs inside `lambda`. -/
noncomputable def initialBlocks :
    Erdos591.StrongIteration.BlockFamily Index Inner Index := by
  let L := Index ×ₗ Inner
  have htype : typeLT L = typeLT Index := by
    change Ordinal.type
      (Prod.Lex ((· < ·) : Index → Index → Prop)
        ((· < ·) : Inner → Inner → Prop)) = _
    rw [Ordinal.type_prod_lex, Ordinal.type_toType, Ordinal.type_toType,
      omegaOmega_mul_lambda]
  let relIso :
      ((· < ·) : L → L → Prop) ≃r
        ((· < ·) : Index → Index → Prop) :=
    Classical.choice (Ordinal.type_eq.mp htype)
  let whole : L ↪o Index :=
    OrderEmbedding.ofStrictMono relIso
      (fun _ _ h ↦ relIso.map_rel_iff.mpr h)
  refine
    { embedding := fun b ↦ OrderEmbedding.ofStrictMono
        (fun y ↦ whole (toLex (b, y))) ?_
      separated := ?_ }
  · intro y z hyz
    apply whole.strictMono
    exact Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl, hyz⟩)
  · intro b c hbc y z
    apply whole.strictMono
    exact Prod.Lex.lt_iff.mpr (Or.inl hbc)

theorem index_countable : Countable Index := by
  rw [← Cardinal.mk_le_aleph0_iff, Cardinal.mk_toType,
    Ordinal.card_omega0_opow (by
      exact pow_ne_zero 2 Ordinal.omega0_ne_zero), pow_two,
    Ordinal.card_mul, Ordinal.card_omega0,
    Cardinal.aleph0_mul_aleph0, max_self]

theorem inner_isSuccLimit : Order.IsSuccLimit (typeLT Inner) := by
  rw [Ordinal.type_toType]
  exact Ordinal.isSuccLimit_opow Ordinal.one_lt_omega0
    Ordinal.isSuccLimit_omega0

/-!
The endpoint relation itself is deliberately not asserted here.  The fixed
reservoir one-step oracle in `EMStepOracle` assumes that a red copy of the
*reservoir* type is excluded.  At the endpoint, excluding a red copy of
`lambda` does not exclude red copies of the smaller `Inner` reservoirs.
Consequently the tempting application of `StrongIteration` with
`B = lambda.ToType` and `Y = (omega^omega).ToType` is invalid.  The lemmas
above are the checked ordinal and finite-indivisibility inputs for the
genuine Schipperus/Darby endpoint fusion.
-/

end Erdos591.Positive
