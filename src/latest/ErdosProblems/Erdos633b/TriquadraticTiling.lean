import ErdosProblems.Erdos633b.TriquadraticParallelogram

/-! Assemble all four congruent subdivisions in the triquadratic construction. -/

namespace Erdos633b

noncomputable def quadratic_patch (T : Triangle) (n : ℕ) (hn : 0 < n) :
    Patch T (T.homothetic (T.points 0) n (by exact_mod_cast hn.ne')).support (n ^ 2) := by
  let d := Classical.choose (quadratic_enlargement T n hn)
  have hd : d.tile = T := Classical.choose_spec (quadratic_enlargement T n hn)
  have result := d.toPatch
  rwa [hd] at result

namespace TriquadraticCoordinates

noncomputable def first_triangle_patch (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) (b : ℕ) (hb : 0 < b) (hbv : (b : ℝ) = c * (1 - s ^ 2)) :
    Patch (reference c s d hc hs hs1 hd) (firstTriangle c s d hc hs hs1 hd).support (b ^ 2) := by
  have result := quadratic_patch (reference c s d hc hs hs1 hd) b hb
  have h0 : (reference c s d hc hs hs1 hd).points 0 = 0 := rfl
  simpa only [firstTriangle, Triangle.support_homothetic, h0, hbv] using result

noncomputable def second_triangle_patch (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) (he : d ^ 2 = 4 - s ^ 2) (b : ℕ) (hb : 0 < b)
    (hbv : (b : ℝ) = c * (1 - s ^ 2)) :
    Patch (reference c s d hc hs hs1 hd) (secondTriangle c s d hc hs hs1 hd he).support
      (b ^ 2) := by
  have result := (first_triangle_patch c s d hc hs hs1 hd b hb hbv).move
    (mirror s d he).toAffineIsometryEquiv
  rwa [← Triangle.support_move] at result

noncomputable def third_triangle_patch (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) (he : d ^ 2 = 4 - s ^ 2) (a : ℕ) (ha : 0 < a)
    (hav : (a : ℝ) = c * s) :
    Patch (reference c s d hc hs hs1 hd) (thirdTriangle c s d hc hs hs1 hd he).support
      (a ^ 2) := by
  have result := (quadratic_patch (reference c s d hc hs hs1 hd) a ha).move (thirdMotion c s d he)
  have h0 : (reference c s d hc hs hs1 hd).points 0 = 0 := rfl
  simpa only [thirdTriangle, Triangle.support_move, Triangle.support_homothetic, h0, hav]
    using result

/-- The complete geometric construction, with the four block counts explicitly summed. -/
noncomputable def triquadratic_patch (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) (he : d ^ 2 = 4 - s ^ 2) (a b j : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hj : 0 < j)
    (hav : (a : ℝ) = c * s) (hbv : (b : ℝ) = c * (1 - s ^ 2))
    (hjv : (j : ℝ) = c * s ^ 2) :
    Patch (reference c s d hc hs hs1 hd) (outer c s d hc hs hs1 hd).support
      (b ^ 2 + b ^ 2 + a ^ 2 + 2 * j * b) := by
  let count : TriquadraticPartition.Piece → ℕ
    | .first => b ^ 2
    | .second => b ^ 2
    | .third => a ^ 2
    | .parallelogram => 2 * j * b
  have hsupports := three_triangle_supports c s d hc hs hs1 hd he
  have patches : ∀ k, Patch (reference c s d hc hs hs1 hd)
      (TriquadraticPartition.region (outer c s d hc hs hs1 hd) (1 - s ^ 2) k) (count k) := by
    intro k
    cases k
    · have result := first_triangle_patch c s d hc hs hs1 hd b hb hbv
      rwa [hsupports.1] at result
    · have result := second_triangle_patch c s d hc hs hs1 hd he b hb hbv
      rwa [hsupports.2.1] at result
    · have result := third_triangle_patch c s d hc hs hs1 hd he a ha hav
      rwa [hsupports.2.2] at result
    · exact fourth_patch c s d hc hs hs1 hd he j b hj hb hjv hbv
  have ht := (parameter_denominator_pos s hs hs1).1
  have ht1 : 1 - s ^ 2 < 1 := by nlinarith [sq_pos_of_pos hs]
  have result := TriquadraticPartition.assemblePatch (outer c s d hc hs hs1 hd)
    (reference c s d hc hs hs1 hd) (1 - s ^ 2) ht ht1 count patches
  have hc : (∑ k, count k) = b ^ 2 + b ^ 2 + a ^ 2 + 2 * j * b := by
    have hu : (Finset.univ : Finset TriquadraticPartition.Piece) =
        {.first, .second, .third, .parallelogram} := rfl
    rw [hu]
    simp [count]
    ring
  rwa [hc] at result

noncomputable def triquadratic_tiling (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) (he : d ^ 2 = 4 - s ^ 2) (a b j : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hj : 0 < j)
    (hav : (a : ℝ) = c * s) (hbv : (b : ℝ) = c * (1 - s ^ 2))
    (hjv : (j : ℝ) = c * s ^ 2) :
    Tiling (outer c s d hc hs hs1 hd) (b ^ 2 + b ^ 2 + a ^ 2 + 2 * j * b) :=
  (triquadratic_patch c s d hc hs hs1 hd he a b j ha hb hj hav hbv hjv).toTiling

theorem triquadratic_nat_count (a b c j : ℕ) (hbj : b + j = c) (hcj : j * c = a ^ 2) :
    b ^ 2 + b ^ 2 + a ^ 2 + 2 * j * b = 2 * c ^ 2 - a ^ 2 := by
  have h : b ^ 2 + b ^ 2 + a ^ 2 + 2 * j * b + a ^ 2 = 2 * c ^ 2 := by
    calc
      _ = 2 * b * (b + j) + 2 * (j * c) := by rw [hcj]; ring
      _ = 2 * b * c + 2 * j * c := by rw [hbj]; ring
      _ = 2 * (b + j) * c := by ring
      _ = 2 * c ^ 2 := by rw [hbj]; ring
  omega

theorem rational_parameter_bounds (a c : ℕ) (ha : 0 < a) (hac : a < c) :
    0 < (c : ℝ) ∧ 0 < (a : ℝ) / c ∧ (a : ℝ) / c < 1 ∧
      0 < 4 - ((a : ℝ) / c) ^ 2 := by
  have hcr : (0 : ℝ) < c := by exact_mod_cast ha.trans hac
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hacr : (a : ℝ) < c := by exact_mod_cast hac
  have hs := div_pos har hcr
  have hs1 := (div_lt_one hcr).mpr hacr
  have hsmall := (parameter_denominator_pos ((a : ℝ) / c) hs hs1).1
  exact ⟨hcr, hs, hs1, by linarith⟩

/-- The explicitly constructed outer triangle for the rational parameter `a / c`. -/
noncomputable def rationalOuter (a c : ℕ) (ha : 0 < a) (hac : a < c) : Triangle :=
  let h := rational_parameter_bounds a c ha hac
  outer c ((a : ℝ) / c) (Real.sqrt (4 - ((a : ℝ) / c) ^ 2))
    h.1 h.2.1 h.2.2.1 (Real.sqrt_pos.mpr h.2.2.2)

/-- A complete finite congruent dissection for every admissible integral side parameter. -/
noncomputable def rational_tiling (a c : ℕ) (ha : 0 < a) (hac : a < c) (hdiv : c ∣ a ^ 2) :
    Tiling (rationalOuter a c ha hac) (2 * c ^ 2 - a ^ 2) := by
  let j := a ^ 2 / c
  let b := c - j
  have hc : 0 < c := ha.trans hac
  have hcj : j * c = a ^ 2 := Nat.div_mul_cancel hdiv
  have hj : 0 < j := Nat.div_pos (Nat.le_of_dvd (pow_pos ha 2) hdiv) hc
  have hjlt : j < c := by
    apply (Nat.div_lt_iff_lt_mul hc).mpr
    nlinarith
  have hb : 0 < b := Nat.sub_pos_of_lt hjlt
  have hbj : b + j = c := Nat.sub_add_cancel hjlt.le
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
  have result := triquadratic_tiling c ((a : ℝ) / c) (Real.sqrt (4 - ((a : ℝ) / c) ^ 2))
    h.1 h.2.1 h.2.2.1 hd he a b j ha hb hj hav hbv hjv
  change Tiling (rationalOuter a c ha hac) (b ^ 2 + b ^ 2 + a ^ 2 + 2 * j * b) at result
  rwa [triquadratic_nat_count a b c j hbj hcj] at result

theorem rationalOuter_hasNonsquareTiling (a c : ℕ) (ha : 0 < a) (hac : a < c)
    (hdiv : c ∣ a ^ 2) (hn : ¬ IsSquare (2 * c ^ 2 - a ^ 2)) :
    HasNonsquareTiling (rationalOuter a c ha hac) :=
  ⟨2 * c ^ 2 - a ^ 2, hn, ⟨rational_tiling a c ha hac hdiv⟩⟩

end TriquadraticCoordinates

end Erdos633b
