import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalExactOne

/-!
# Degree-two exactness of the actual signed total complex

A closed triple is simplified successively using its original vertical
degree-two and degree-one primitives. The remaining class is the image
of a closed element in the original horizontal row; its actual row
primitive completes the total primitive.
-/

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalComplex

universe u

variable {R00 R10 R01 R20 R11 R02 R30 R21 R12 R03 : Type u}
  [AddCommGroup R00] [AddCommGroup R10] [AddCommGroup R01]
  [AddCommGroup R20] [AddCommGroup R11] [AddCommGroup R02]
  [AddCommGroup R30] [AddCommGroup R21] [AddCommGroup R12] [AddCommGroup R03]
  {D : Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03}
  {S0 S1 S2 S3 : Type u} [AddCommGroup S0] [AddCommGroup S1]
  [AddCommGroup S2] [AddCommGroup S3]
  (A : AugmentedColumns D S0 S1 S2 S3)

namespace AugmentedColumns

/-- The actual total complex is exact in degree two when the original
horizontal row is exact there. -/
theorem exact_two (hrow : Function.Exact A.d1 A.d2) : Function.Exact D.d1 D.d2 := by
  rintro ⟨c, d, e⟩
  constructor
  · intro hx
    have hc0 : D.v20 c = 0 := congrArg Prod.fst hx
    have hcd : D.h20 c + D.v11 d = 0 :=
      congrArg (fun y : D.Three => y.2.1) hx
    have hde : -D.h11 d + D.v02 e = 0 :=
      congrArg (fun y : D.Three => y.2.2.1) hx
    have he0 : D.h02 e = 0 := congrArg (fun y : D.Three => y.2.2.2) hx
    have hde' : D.v02 e = D.h11 d := by
      have h := congrArg (fun x => D.h11 d + x) hde
      simpa only [← add_assoc, add_neg_cancel, zero_add, add_zero] using h
    obtain ⟨a, ha⟩ := (A.column20 c).mp hc0
    let d' := d + D.h10 a
    have hd' : D.v11 d' = 0 := by
      dsimp [d']
      rw [map_add, D.v11_h10, ha]
      exact (add_comm _ _).trans hcd
    obtain ⟨b, hb⟩ := (A.column11 d').mp hd'
    let e' := e - D.h01 b
    have he' : D.v02 e' = 0 := by
      dsimp [e']
      rw [map_sub, D.v02_h01, hb]
      dsimp [d']
      rw [map_add, D.h11_h10, add_zero, hde', sub_self]
    obtain ⟨s2, hs2⟩ := (A.column02 e').mp he'
    have hds2 : A.d2 s2 = 0 := A.injective3 (by
      calc
        A.i3 (A.d2 s2) = D.h02 (A.i2 s2) := (A.h02_i2 s2).symm
        _ = D.h02 e' := congrArg D.h02 hs2
        _ = 0 := by dsimp [e']; rw [map_sub, he0, D.h02_h01, sub_self]
        _ = A.i3 0 := (map_zero A.i3).symm)
    obtain ⟨s1, hs1⟩ := (hrow s2).mp hds2
    refine ⟨(a, b + A.i1 s1), ?_⟩
    apply Prod.ext
    · exact ha
    · apply Prod.ext
      · change -D.h10 a + D.v01 (b + A.i1 s1) = d
        rw [map_add, A.v01_i1, add_zero, hb]
        dsimp [d']
        abel
      · change D.h01 (b + A.i1 s1) = e
        rw [map_add, A.h01_i1, hs1, hs2]
        dsimp [e']
        abel
  · rintro ⟨y, hy⟩
    exact hy ▸ D.d2_d1 y

end AugmentedColumns

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalComplex
