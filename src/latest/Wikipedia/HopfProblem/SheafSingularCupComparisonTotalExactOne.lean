import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalExactBasic
import Mathlib.Tactic.Abel

/-!
# Initial and degree-one exactness of the actual signed total complex

The proofs are explicit diagram chases through the original vertical
columns and horizontal row. No total-complex exactness or comparison
theorem is assumed.
-/

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalComplex

universe u

private theorem cancel_neg_add {G : Type*} [AddCommGroup G]
    (a b : G) (h : -a + b = 0) : b = a := by
  have h' := congrArg (fun x => a + x) h
  simpa only [← add_assoc, add_neg_cancel, zero_add, add_zero] using h'

variable {R00 R10 R01 R20 R11 R02 R30 R21 R12 R03 : Type u}
  [AddCommGroup R00] [AddCommGroup R10] [AddCommGroup R01]
  [AddCommGroup R20] [AddCommGroup R11] [AddCommGroup R02]
  [AddCommGroup R30] [AddCommGroup R21] [AddCommGroup R12] [AddCommGroup R03]
  {D : Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03}
  {S0 S1 S2 S3 : Type u} [AddCommGroup S0] [AddCommGroup S1]
  [AddCommGroup S2] [AddCommGroup S3]
  (A : AugmentedColumns D S0 S1 S2 S3)

namespace AugmentedColumns

/-- The actual augmentation is exact at total degree zero. -/
theorem exact_zero {F : Type u} [AddCommGroup F] (ι : F →+ S0)
    (hrow : Function.Exact ι A.d0) : Function.Exact (A.i0.comp ι) D.d0 := by
  intro x
  constructor
  · intro hx
    have hxv : D.v00 x = 0 := congrArg Prod.fst hx
    have hxh : D.h00 x = 0 := congrArg Prod.snd hx
    obtain ⟨s, hs⟩ := (A.column00 x).mp hxv
    have hds : A.d0 s = 0 := A.injective1 (by
      calc
        A.i1 (A.d0 s) = D.h00 (A.i0 s) := (A.h00_i0 s).symm
        _ = D.h00 x := congrArg D.h00 hs
        _ = 0 := hxh
        _ = A.i1 0 := (map_zero A.i1).symm)
    obtain ⟨f, hf⟩ := (hrow s).mp hds
    refine ⟨f, ?_⟩
    change A.i0 (ι f) = x
    rw [hf, hs]
  · rintro ⟨f, rfl⟩
    change D.d0 (A.i0 (ι f)) = 0
    simp [hrow.apply_apply_eq_zero f]

/-- Degree-one total cocycles have actual total primitives whenever
the original horizontal degree-one row is exact. -/
theorem exact_one (hrow : Function.Exact A.d0 A.d1) : Function.Exact D.d0 D.d1 := by
  rintro ⟨a, b⟩
  constructor
  · intro hx
    have ha0 : D.v10 a = 0 := congrArg Prod.fst hx
    have hab : -D.h10 a + D.v01 b = 0 :=
      congrArg (fun y : D.Two => y.2.1) hx
    have hb0 : D.h01 b = 0 := congrArg (fun y : D.Two => y.2.2) hx
    have hab' : D.v01 b = D.h10 a := cancel_neg_add _ _ hab
    obtain ⟨r, hr⟩ := (A.column10 a).mp ha0
    let b' := b - D.h00 r
    have hb' : D.v01 b' = 0 := by
      dsimp [b']
      rw [map_sub, D.v01_h00, hr, hab', sub_self]
    obtain ⟨s1, hs1⟩ := (A.column01 b').mp hb'
    have hds1 : A.d1 s1 = 0 := A.injective2 (by
      calc
        A.i2 (A.d1 s1) = D.h01 (A.i1 s1) := (A.h01_i1 s1).symm
        _ = D.h01 b' := congrArg D.h01 hs1
        _ = 0 := by dsimp [b']; rw [map_sub, hb0, D.h01_h00, sub_self]
        _ = A.i2 0 := (map_zero A.i2).symm)
    obtain ⟨s0, hs0⟩ := (hrow s1).mp hds1
    refine ⟨r + A.i0 s0, ?_⟩
    apply Prod.ext
    · change D.v00 (r + A.i0 s0) = a
      rw [map_add, A.v00_i0, add_zero, hr]
    · change D.h00 (r + A.i0 s0) = b
      rw [map_add, A.h00_i0, hs0, hs1]
      dsimp [b']
      abel
  · rintro ⟨r, hr⟩
    exact hr ▸ D.d1_d0 r

end AugmentedColumns

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalComplex
