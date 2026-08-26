import ErdosProblems.Erdos633b.TrapezoidMetric
import ErdosProblems.Erdos633b.PatchAssembly

/-! The complete basic group-2 trapezoid patch, with its exact finite count. -/

namespace Erdos633b.Sixty

noncomputable def basic_trapezoid_patch (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hrel : (c : ℝ) ^ 2 = (a : ℝ) ^ 2 + (a : ℝ) * b + (b : ℝ) ^ 2) :
    Patch (groupTwoReference d hd a b (by exact_mod_cast ha) (by exact_mod_cast hb))
      (TrapezoidPartition.trapezoidSet (frame d hd) ((a : ℝ) ^ 2 + (b : ℝ) ^ 2)
        ((a : ℝ) * b)) (a ^ 2 + b ^ 2 + c ^ 2) := by
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have hcr : (0 : ℝ) < c := by exact_mod_cast hc
  let R := groupTwoReference d hd a b har hbr
  let count : TrapezoidPartition.Piece → ℕ
    | .left => a ^ 2
    | .right => b ^ 2
    | .middle => c ^ 2
  have patches : ∀ k, Patch R
      (TrapezoidPartition.region (frame d hd) ((a : ℝ) ^ 2) ((b : ℝ) ^ 2)
        ((a : ℝ) * b) k) (count k) := by
    intro k
    cases k
    · have result := quadratic_patch_congruent R
        (leftTriangle d hd ((a : ℝ) ^ 2) ((a : ℝ) * b) (sq_pos_of_pos har) (mul_pos har hbr))
        a ha (basic_left_sides d hd he a b c har hbr hrel)
      rwa [leftTriangle_support d hd ((a : ℝ) ^ 2) ((b : ℝ) ^ 2) ((a : ℝ) * b)
        (sq_pos_of_pos har) (mul_pos har hbr)] at result
    · have result := quadratic_patch_congruent R
        (rightTriangle d hd ((a : ℝ) ^ 2) ((b : ℝ) ^ 2) ((a : ℝ) * b)
          (sq_pos_of_pos hbr) (mul_pos har hbr))
        b hb (basic_right_sides d hd he a b c har hbr hrel)
      rwa [rightTriangle_support d hd ((a : ℝ) ^ 2) ((b : ℝ) ^ 2) ((a : ℝ) * b)
        (sq_pos_of_pos hbr) (mul_pos har hbr)] at result
    · have result := quadratic_patch_congruent R
        (middleTriangle d hd ((a : ℝ) ^ 2) ((b : ℝ) ^ 2) ((a : ℝ) * b)
          (sq_pos_of_pos har) (sq_pos_of_pos hbr) (mul_pos har hbr))
        c hc (basic_middle_sides d hd he a b c har hbr hcr hrel)
      rwa [middleTriangle_support d hd ((a : ℝ) ^ 2) ((b : ℝ) ^ 2) ((a : ℝ) * b)
        (sq_pos_of_pos har) (sq_pos_of_pos hbr) (mul_pos har hbr)] at result
  have hcount : (∑ k, count k) = a ^ 2 + b ^ 2 + c ^ 2 := by
    have hu : (Finset.univ : Finset TrapezoidPartition.Piece) = {.left, .right, .middle} := rfl
    rw [hu]
    simp [count, Nat.add_assoc]
  have result := TrapezoidPartition.assemble (frame d hd) R ((a : ℝ) ^ 2) ((b : ℝ) ^ 2)
    ((a : ℝ) * b) (sq_pos_of_pos har) (sq_pos_of_pos hbr) (mul_pos har hbr) count patches
  rwa [hcount] at result

end Erdos633b.Sixty
