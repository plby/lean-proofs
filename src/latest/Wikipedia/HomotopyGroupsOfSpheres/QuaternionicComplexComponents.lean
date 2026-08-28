import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexCentralizer

/-!
# Complex components of the quaternionic Schur expression

Write a quaternion as `u + v j`, with `u,v : ℂ`. The formulas below split
the section correction into these two components while retaining the
noncommutative multiplication order.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexPlane

open QuaternionicScalars

local notation "ℍ" => Quaternion ℝ

theorem complexPart_coeComplex (z : ℂ) : complexPart (z : ℍ) = z := rfl

theorem coordinate_coeComplex (z : ℂ) : coordinate (z : ℍ) = 0 := rfl

theorem complexPart_embed (z : ℂ) : complexPart (embed z) = 0 := by
  rw [embed_eq_mk]
  rfl

theorem complexPart_add (q r : ℍ) : complexPart (q + r) = complexPart q + complexPart r := rfl

theorem coordinate_add (q r : ℍ) : coordinate (q + r) = coordinate q + coordinate r := rfl

theorem coeComplex_add_embed (q : ℍ) : (complexPart q : ℍ) + embed (coordinate q) = q := by
  rw [embed_eq_mk]
  apply Quaternion.ext
  · change q.re + 0 = q.re
    exact add_zero _
  · change q.imI + 0 = q.imI
    exact add_zero _
  · change 0 + q.imJ = q.imJ
    exact zero_add _
  · change 0 + q.imK = q.imK
    exact zero_add _

theorem embed_sub (z w : ℂ) : embed (z - w) = embed z - embed w := by
  change Quaternion.ofComplex (z - w) * j = _
  rw [map_sub, sub_mul]
  rfl

theorem embed_real_smul (d : ℝ) (z : ℂ) : embed (d • z) = d • embed z := by
  change Quaternion.ofComplex (d • z) * j = _
  rw [map_smul, smul_mul_assoc]
  rfl

theorem coeComplex_real_smul (d : ℝ) (z : ℂ) : ((d • z : ℂ) : ℍ) = d • (z : ℍ) :=
  map_smul Quaternion.ofComplex d z

theorem coeComplex_mul_embed (z w : ℂ) : (z : ℍ) * embed w = embed (z * w) := by
  simp only [embed, Quaternion.coeComplex_mul, mul_assoc]

theorem embed_schur_product (x z y : ℂ) :
    embed x * (1 - embed z) * embed y =
      -((x * star y : ℂ) : ℍ) + embed (x * star z * y) := by
  rw [mul_sub, mul_one, sub_mul, embed_mul_embed, embed_mul_embed,
    neg_mul, coeComplex_mul_embed, sub_neg_eq_add]

theorem schur_split (d : ℝ) (w x z y : ℂ) :
    embed w - embed x * (d • (1 - embed z)) * embed y =
      ((d • (x * star y) : ℂ) : ℍ) + embed (w - d • (x * star z * y)) := by
  rw [mul_smul_comm, smul_mul_assoc, embed_schur_product,
    smul_add, smul_neg, coeComplex_real_smul, embed_sub, embed_real_smul]
  abel

theorem complexPart_schur (d : ℝ) (w x z y : ℂ) :
    complexPart (embed w - embed x * (d • (1 - embed z)) * embed y) = d • (x * star y) := by
  rw [schur_split, complexPart_add, complexPart_coeComplex, complexPart_embed, add_zero]

theorem coordinate_schur (d : ℝ) (w x z y : ℂ) :
    coordinate (embed w - embed x * (d • (1 - embed z)) * embed y) =
      w - d • (x * star z * y) := by
  rw [schur_split, coordinate_add, coordinate_coeComplex, coordinate_embed, zero_add]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexPlane
