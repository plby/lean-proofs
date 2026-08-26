import ErdosProblems.Erdos941.PairGeometry
import ErdosProblems.Erdos941.EulerTripleMap

/-! # The local residue constraint used in trajectory shadowing -/

namespace Erdos941

private theorem shadow_residue_kernel (a b : Axis) (hab : a ≠ b)
    (x y z u v w : ZMod 3)
    (hn : x ^ 2 + y ^ 2 + z ^ 2 = 2)
    (ha : x + (sign a.1 : ZMod 3) * y + (sign a.2 : ZMod 3) * z = 0)
    (hb : x + (sign b.1 : ZMod 3) * y + (sign b.2 : ZMod 3) * z = 0)
    (hca : u + (sign a.1 : ZMod 3) * v + (sign a.2 : ZMod 3) * w = 0)
    (hcb : u + (sign b.1 : ZMod 3) * v + (sign b.2 : ZMod 3) * w = 0)
    (hdot : x * u + y * v + z * w = 0) : u = 0 ∧ v = 0 ∧ w = 0 := by
  rcases a with ⟨a1, a2⟩
  rcases b with ⟨b1, b2⟩
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;>
    simp only [ne_eq, Prod.mk.injEq, Bool.false_eq_true, Bool.true_eq_false,
      and_self, not_true_eq_false, not_false_eq_true, and_false, false_and,
      Bool.not_eq_true, sign, ↓reduceIte, Int.cast_neg, Int.cast_one, one_mul,
      neg_one_mul] at hab ha hb hca hcb
  all_goals try contradiction
  all_goals revert x y z u v w; decide

theorem shadow_local_divisible {a b : Axis} (hab : a ≠ b) {v c : Triple}
    (hn : tripleNorm v % 3 = 2) (ha : Admissible a v) (hb : Admissible b v)
    (hca : Admissible a c) (hcb : Admissible b c) (hc : dot3 v c = 0) :
    TripleDivisible 3 c := by
  have hnorm : (v.1 : ZMod 3) ^ 2 + (v.2.1 : ZMod 3) ^ 2 + (v.2.2 : ZMod 3) ^ 2 = 2 := by
    have hd : (3 : ℤ) ∣ tripleNorm v - 2 := by omega
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd (tripleNorm v - 2) 3).mpr hd
    push_cast at hh
    simpa [tripleNorm, norm3] using sub_eq_zero.mp hh
  have hcast {a : Axis} {v : Triple} (h : Admissible a v) :
      (v.1 : ZMod 3) + (sign a.1 : ZMod 3) * v.2.1 + (sign a.2 : ZMod 3) * v.2.2 = 0 := by
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd (axisDot a v) 3).mpr h
    simpa only [axisDot, Int.cast_add, Int.cast_mul] using hh
  have hdot : (v.1 : ZMod 3) * c.1 + (v.2.1 : ZMod 3) * c.2.1 +
      (v.2.2 : ZMod 3) * c.2.2 = 0 := by
    have hh := congrArg (fun x : ℤ => (x : ZMod 3)) hc
    simpa only [dot3, Int.cast_add, Int.cast_mul, Int.cast_zero] using hh
  obtain ⟨h1, h2, h3⟩ := shadow_residue_kernel a b hab _ _ _ _ _ _ hnorm
    (hcast ha) (hcast hb) (hcast hca) (hcast hcb) hdot
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd c.1 3).mp h1,
    (ZMod.intCast_zmod_eq_zero_iff_dvd c.2.1 3).mp h2,
    (ZMod.intCast_zmod_eq_zero_iff_dvd c.2.2 3).mp h3⟩

end Erdos941
