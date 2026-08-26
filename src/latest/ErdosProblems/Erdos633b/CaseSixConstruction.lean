import ErdosProblems.Erdos633b.CaseSixAngles
import ErdosProblems.Erdos633b.DoubledSubdivision

/-! A genuine finite tiling for the entire group-1 case-(6) parameter interval. -/

namespace Erdos633b.CaseSixCoordinates

open TriquadraticCoordinates

noncomputable def attached_patch (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) (he : d ^ 2 = 4 - s ^ 2) (q : ℕ) (hq : 0 < q)
    (hqv : (q : ℝ) = c * (2 - s ^ 2)) :
    Patch (reference c s d hc hs hs1 hd) (attached c s d hc hs hs1 hd).support (q ^ 2) := by
  apply quadratic_patch_permuted _ _ (Equiv.swap 0 1) q hq
  intro i
  rw [attached_sides c s d hc hs hs1 hd he, reference_sides c s d hc hs hs1 hd he, hqv]
  congr 1
  fin_cases i <;> rfl

noncomputable def group_one_tiling (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) (he : d ^ 2 = 4 - s ^ 2) (a b j q : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hj : 0 < j) (hq : 0 < q)
    (hav : (a : ℝ) = c * s) (hbv : (b : ℝ) = c * (1 - s ^ 2))
    (hjv : (j : ℝ) = c * s ^ 2) (hqv : (q : ℝ) = c * (2 - s ^ 2)) :
    Tiling (outer c s d hc hs hs1 hd) (b ^ 2 + b ^ 2 + a ^ 2 + 2 * j * b + q ^ 2) := by
  let R := reference c s d hc hs hs1 hd
  let S := base c s d hc hs hs1 hd
  let U := outer c s d hc hs hs1 hd
  let t := 2 - s ^ 2
  have ht : 0 < t := (parameter_denominator_pos s hs hs1).2
  have old : Patch R S.support (b ^ 2 + b ^ 2 + a ^ 2 + 2 * j * b) := by
    simpa only [S, base, Triangle.support_reindex] using
      triquadratic_patch c s d hc hs hs1 hd he a b j ha hb hj hav hbv hjv
  have first : Patch R (U.edgeFirst (1 / (1 + t)) (Triangle.extension_weight_pos t ht)).support
      (b ^ 2 + b ^ 2 + a ^ 2 + 2 * j * b) := by
    have heq : U.edgeFirst (1 / (1 + t)) (Triangle.extension_weight_pos t ht) = S :=
      S.edgeExtension_first t ht
    rw [heq]
    exact old
  have second : Patch R (U.edgeSecond (1 / (1 + t))
      (Triangle.extension_weight_lt_one t ht)).support (q ^ 2) :=
    attached_patch c s d hc hs hs1 hd he q hq hqv
  exact edge_patch_assemble U R (1 / (1 + t)) (Triangle.extension_weight_pos t ht)
    (Triangle.extension_weight_lt_one t ht) _ _ first second

theorem integer_count (a b c j : ℕ) (hbj : b + j = c) (hcj : j * c = a ^ 2) :
    b ^ 2 + b ^ 2 + a ^ 2 + 2 * j * b + (c + b) ^ 2 = (c + b) * (2 * c + b) := by
  have hh : b ^ 2 + b ^ 2 + a ^ 2 + 2 * j * b = c * (c + b) := by
    rw [← hcj, ← hbj]
    ring
  rw [hh]
  ring

noncomputable def rationalOuter (a c : ℕ) (ha : 0 < a) (hac : a < c) : Triangle :=
  let h := rational_parameter_bounds a c ha hac
  outer c ((a : ℝ) / c) (Real.sqrt (4 - ((a : ℝ) / c) ^ 2))
    h.1 h.2.1 h.2.2.1 (Real.sqrt_pos.mpr h.2.2.2)

noncomputable def integer_tiling (a b c j : ℕ) (ha : 0 < a) (hb : 0 < b) (hj : 0 < j)
    (hac : a < c) (hbj : b + j = c) (hcj : j * c = a ^ 2) :
    Tiling (rationalOuter a c ha hac) ((c + b) * (2 * c + b)) := by
  have hc : 0 < c := ha.trans hac
  have h := rational_parameter_bounds a c ha hac
  have hd := Real.sqrt_pos.mpr h.2.2.2
  have he := Real.sq_sqrt h.2.2.2.le
  have hav : (a : ℝ) = (c : ℝ) * ((a : ℝ) / c) := by field_simp
  have hjv : (j : ℝ) = (c : ℝ) * ((a : ℝ) / c) ^ 2 := by
    apply mul_right_cancel₀ h.1.ne'
    calc
      (j : ℝ) * c = (a : ℝ) ^ 2 := by exact_mod_cast hcj
      _ = ((c : ℝ) * ((a : ℝ) / c) ^ 2) * c := by field_simp
  have hbv : (b : ℝ) = (c : ℝ) * (1 - ((a : ℝ) / c) ^ 2) := by
    have hsum : (b : ℝ) + (j : ℝ) = c := by exact_mod_cast hbj
    nlinarith
  have hqv : ((c + b : ℕ) : ℝ) = (c : ℝ) * (2 - ((a : ℝ) / c) ^ 2) := by
    push_cast
    rw [hbv]
    ring
  have result := group_one_tiling c ((a : ℝ) / c) (Real.sqrt (4 - ((a : ℝ) / c) ^ 2))
    h.1 h.2.1 h.2.2.1 hd he a b j (c + b) ha hb hj (by omega) hav hbv hjv hqv
  change Tiling (rationalOuter a c ha hac)
    (b ^ 2 + b ^ 2 + a ^ 2 + 2 * j * b + (c + b) ^ 2) at result
  rwa [integer_count a b c j hbj hcj] at result

theorem rationalOuter_relations (a c : ℕ) (ha : 0 < a) (hac : a < c) :
    (rationalOuter a c ha hac).angle 0 = 2 * (rationalOuter a c ha hac).angle 1 ∧
      2 * Real.sin ((rationalOuter a c ha hac).angle 1 / 2) = (a : ℝ) / c := by
  have h := rational_parameter_bounds a c ha hac
  exact outer_angle_relations c ((a : ℝ) / c) (Real.sqrt (4 - ((a : ℝ) / c) ^ 2))
    h.1 h.2.1 h.2.2.1 (Real.sqrt_pos.mpr h.2.2.2) (Real.sq_sqrt h.2.2.2.le)

end Erdos633b.CaseSixCoordinates
