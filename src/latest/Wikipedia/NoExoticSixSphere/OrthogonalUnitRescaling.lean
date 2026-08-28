import Wikipedia.NoExoticSixSphere.OrthogonalUnitExtension

/-! # Nonzero rescaling of the appended column preserves its full span -/

noncomputable section

namespace NoExoticSixSphere.OrthogonalUnitExtension

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem range_operator_smul (B : E →L[ℝ] F) (ν : F) {c : ℝ} (hc : c ≠ 0) :
    (operator B (c • ν)).range = (operator B ν).range := by
  ext y
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨WithLp.toLp 2 (v.fst, v.snd * c), ?_⟩
    change B v.fst + (v.snd * c) • ν = y
    change B v.fst + v.snd • (c • ν) = y at hv
    simpa only [smul_smul] using hv
  · rintro ⟨v, hv⟩
    refine ⟨WithLp.toLp 2 (v.fst, v.snd / c), ?_⟩
    change B v.fst + (v.snd / c) • (c • ν) = y
    rw [smul_smul, div_mul_cancel₀ _ hc]
    exact hv

theorem injective_operator_smul (B : E →L[ℝ] F) (ν : F) {c : ℝ} (hc : c ≠ 0)
    (hi : Function.Injective (operator B ν)) : Function.Injective (operator B (c • ν)) := by
  have hscale (v : WithLp 2 (E × ℝ)) : operator B (c • ν) v =
      operator B ν (WithLp.toLp 2 (v.fst, v.snd * c)) := by
    change B v.fst + v.snd • (c • ν) = B v.fst + (v.snd * c) • ν
    rw [smul_smul]
  intro u v he
  have h := hi ((hscale u).symm.trans (he.trans (hscale v)))
  have hb := congrArg (fun z : WithLp 2 (E × ℝ) ↦ z.fst) h
  have hs := congrArg (fun z : WithLp 2 (E × ℝ) ↦ z.snd) h
  change u.fst = v.fst at hb
  change u.snd * c = v.snd * c at hs
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).injective
  exact Prod.ext hb (mul_right_cancel₀ hc hs)

end NoExoticSixSphere.OrthogonalUnitExtension
