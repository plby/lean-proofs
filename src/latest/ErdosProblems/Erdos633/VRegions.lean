import ErdosProblems.Erdos633.Parallelogram

/-!
# The four regions of the group-one V construction

These are normalized coordinates in the standard triangle. For `0 < b < 1`,
the construction uses `D=(b,0)`, `Q=(b²/(1+b),b/(1+b))`, and
`E=(1/(1+b),b/(1+b))`. The four closed regions cover the triangle and have
pairwise disjoint interiors.
-/

namespace Erdos633

noncomputable def linearXMinusY (b : ℝ) : ℂ →L[ℝ] ℝ :=
  Complex.reCLM - b • Complex.imCLM

noncomputable def linearXPlusY (b : ℝ) : ℂ →L[ℝ] ℝ :=
  Complex.reCLM + b • Complex.imCLM

theorem linearXMinusY_apply (b : ℝ) (z : ℂ) : linearXMinusY b z = z.re - b * z.im := rfl
theorem linearXPlusY_apply (b : ℝ) (z : ℂ) : linearXPlusY b z = z.re + b * z.im := rfl

theorem linearXMinusY_surjective (b : ℝ) : Function.Surjective (linearXMinusY b) := by
  intro r
  exact ⟨(r : ℂ), by simp [linearXMinusY_apply]⟩

theorem linearXPlusY_surjective (b : ℝ) : Function.Surjective (linearXPlusY b) := by
  intro r
  exact ⟨(r : ℂ), by simp [linearXPlusY_apply]⟩

theorem convex_linear_le (f : ℂ →L[ℝ] ℝ) (a : ℝ) : Convex ℝ {z | f z ≤ a} :=
  convex_halfSpace_le ⟨f.map_add, f.map_smul⟩ a

theorem convex_linear_ge (f : ℂ →L[ℝ] ℝ) (a : ℝ) : Convex ℝ {z | a ≤ f z} :=
  convex_halfSpace_ge ⟨f.map_add, f.map_smul⟩ a

theorem separated_interiors {S U : Set ℂ} (f : ℂ →L[ℝ] ℝ)
    (hf : Function.Surjective f) (a : ℝ)
    (hS : S ⊆ {z | f z ≤ a}) (hU : U ⊆ {z | a ≤ f z}) :
    Disjoint (interior S) (interior U) := by
  apply Set.disjoint_left.mpr
  intro z hz hw
  have hl := interior_mono hS hz
  have hr := interior_mono hU hw
  change z ∈ interior (f ⁻¹' Set.Iic a) at hl
  change z ∈ interior (f ⁻¹' Set.Ici a) at hr
  rw [f.interior_preimage hf, interior_Iic] at hl
  rw [f.interior_preimage hf, interior_Ici] at hr
  change f z < a at hl
  change a < f z at hr
  exact (not_lt_of_gt hr) hl

def vLowerRegion (b : ℝ) : Set ℂ :=
  {z | 0 ≤ z.im ∧ 0 ≤ z.re - b * z.im ∧ z.re + z.im ≤ b}

def vLeftRegion (b : ℝ) : Set ℂ :=
  {z | 0 ≤ z.re ∧ z.re - b * z.im ≤ 0 ∧ z.re + b ^ 2 * z.im ≤ b ^ 2}

def vUpperRegion (b : ℝ) : Set ℂ :=
  {z | b / (1 + b) ≤ z.im ∧ b ^ 2 ≤ z.re + b ^ 2 * z.im ∧ z.re + z.im ≤ 1}

def vParallelogramRegion (b : ℝ) : Set ℂ :=
  {z | 0 ≤ z.im ∧ z.im ≤ b / (1 + b) ∧ b ≤ z.re + z.im ∧ z.re + z.im ≤ 1}

theorem vLowerRegion_convex (b : ℝ) : Convex ℝ (vLowerRegion b) := by
  have hc : Convex ℝ {z : ℂ | z.re + z.im ≤ b} := by
    simpa only [linearXPlusY_apply, one_mul] using convex_linear_le (linearXPlusY 1) b
  exact (convex_linear_ge Complex.imCLM 0).inter
    ((convex_linear_ge (linearXMinusY b) 0).inter hc)

theorem vLeftRegion_convex (b : ℝ) : Convex ℝ (vLeftRegion b) := by
  exact (convex_linear_ge Complex.reCLM 0).inter
    ((convex_linear_le (linearXMinusY b) 0).inter (convex_linear_le (linearXPlusY (b ^ 2)) (b ^ 2)))

theorem vUpperRegion_convex (b : ℝ) : Convex ℝ (vUpperRegion b) := by
  have hc : Convex ℝ {z : ℂ | z.re + z.im ≤ 1} := by
    simpa only [linearXPlusY_apply, one_mul] using convex_linear_le (linearXPlusY 1) 1
  exact (convex_linear_ge Complex.imCLM (b / (1 + b))).inter
    ((convex_linear_ge (linearXPlusY (b ^ 2)) (b ^ 2)).inter hc)

theorem vRegions_cover (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    ((vLowerRegion b ∪ vLeftRegion b) ∪ vUpperRegion b) ∪ vParallelogramRegion b =
      standardTriangle.carrier := by
  have hd : 0 < 1 + b := by linarith
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb0
  have hb2lt : b ^ 2 < 1 := by nlinarith
  have hq : 0 < b / (1 + b) := div_pos hb0 hd
  have hqb : b / (1 + b) < b := by
    apply (div_lt_iff₀ hd).mpr
    nlinarith
  rw [standardTriangle_carrier]
  ext z
  simp only [Set.mem_union, vLowerRegion, vLeftRegion, vUpperRegion,
    vParallelogramRegion, Set.mem_ofPred_eq]
  constructor
  · rintro (((h | h) | h) | h)
    · have hm := mul_nonneg hb0.le h.1
      exact ⟨by linarith [h.2.1], h.1, by linarith [h.2.2]⟩
    · have hy : 0 ≤ z.im := by nlinarith [h.1, h.2.1]
      have hy1 : z.im ≤ 1 := by nlinarith [h.1, h.2.2]
      have hm := mul_nonneg (show 0 ≤ 1 - b ^ 2 by linarith) (show 0 ≤ 1 - z.im by linarith)
      exact ⟨h.1, hy, by nlinarith [h.2.2]⟩
    · have hm : 0 ≤ (1 - b ^ 2) * (1 - z.im) := by nlinarith [h.2.1, h.2.2]
      have hy1 : z.im ≤ 1 := by
        have := nonneg_of_mul_nonneg_right hm (show 0 < 1 - b ^ 2 by linarith)
        linarith
      have hx := mul_nonneg hb2.le (show 0 ≤ 1 - z.im by linarith)
      exact ⟨by nlinarith [h.2.1], by linarith [h.1], h.2.2⟩
    · exact ⟨by linarith [h.2.1, h.2.2.1], h.1, h.2.2.2⟩
  · rintro ⟨hx, hy, hs⟩
    by_cases hlow : z.im ≤ b / (1 + b)
    · have hyb : z.im * (1 + b) ≤ b := (le_div_iff₀ hd).mp hlow
      by_cases hsum : z.re + z.im ≤ b
      · by_cases hside : 0 ≤ z.re - b * z.im
        · exact Or.inl (Or.inl (Or.inl ⟨hy, hside, hsum⟩))
        · have hm := mul_le_mul_of_nonneg_left hyb hb0.le
          exact Or.inl (Or.inl (Or.inr ⟨hx, by linarith, by nlinarith⟩))
      · exact Or.inr ⟨hy, hlow, by linarith, hs⟩
    · have hyb : b < z.im * (1 + b) := (div_lt_iff₀ hd).mp (lt_of_not_ge hlow)
      by_cases hside : z.re + b ^ 2 * z.im ≤ b ^ 2
      · have hm := mul_lt_mul_of_pos_left hyb hb0
        exact Or.inl (Or.inl (Or.inr ⟨hx, by nlinarith, hside⟩))
      · exact Or.inl (Or.inr ⟨by linarith, by linarith, hs⟩)

theorem vLower_left_disjoint (b : ℝ) :
    Disjoint (interior (vLowerRegion b)) (interior (vLeftRegion b)) := by
  apply (separated_interiors (linearXMinusY b) (linearXMinusY_surjective b) 0
    (fun _ h => h.2.1) (fun _ h => h.2.1)).symm

theorem vLeft_upper_disjoint (b : ℝ) :
    Disjoint (interior (vLeftRegion b)) (interior (vUpperRegion b)) := by
  exact separated_interiors (linearXPlusY (b ^ 2)) (linearXPlusY_surjective _) (b ^ 2)
    (fun _ h => h.2.2) (fun _ h => h.2.1)

theorem vLower_parallelogram_disjoint (b : ℝ) :
    Disjoint (interior (vLowerRegion b)) (interior (vParallelogramRegion b)) := by
  apply separated_interiors (linearXPlusY 1) (linearXPlusY_surjective _) b
  · intro z hz
    simpa [linearXPlusY_apply] using hz.2.2
  · intro z hz
    simpa [linearXPlusY_apply] using hz.2.2.1

theorem vLower_upper_disjoint (b : ℝ) (hb0 : 0 < b) :
    Disjoint (interior (vLowerRegion b)) (interior (vUpperRegion b)) := by
  have hf : Function.Surjective Complex.imCLM := fun r => ⟨⟨0, r⟩, rfl⟩
  apply separated_interiors Complex.imCLM hf (b / (1 + b))
  · intro z hz
    apply (le_div_iff₀ (by linarith : 0 < 1 + b)).mpr
    change z.im * (1 + b) ≤ b
    nlinarith [hz.2.1, hz.2.2]
  · exact fun _ h => h.1

theorem vLeft_parallelogram_disjoint (b : ℝ) (hb0 : 0 < b) :
    Disjoint (interior (vLeftRegion b)) (interior (vParallelogramRegion b)) := by
  apply separated_interiors (linearXMinusY b) (linearXMinusY_surjective b) 0
  · exact fun _ h => h.2.1
  · intro z hz
    have hyb := (le_div_iff₀ (by linarith : 0 < 1 + b)).mp hz.2.1
    change 0 ≤ z.re - b * z.im
    nlinarith [hz.2.2.1]

theorem vUpper_parallelogram_disjoint (b : ℝ) :
    Disjoint (interior (vUpperRegion b)) (interior (vParallelogramRegion b)) := by
  have hf : Function.Surjective Complex.imCLM := fun r => ⟨⟨0, r⟩, rfl⟩
  exact (separated_interiors Complex.imCLM hf (b / (1 + b))
    (fun _ h => h.2.1) (fun _ h => h.1)).symm

end Erdos633
