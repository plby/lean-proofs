import Wikipedia.NoExoticSixSphere.FixedColumnBlock
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Splitting off a complex line in orthogonal coordinates

In coordinates `ℝ ⊕ ℝ ⊕ F`, a skew-adjoint operator squaring to minus
identity and sending the first unit vector to the second is the standard
quarter-turn on the first two coordinates plus a complex structure on `F`.
The restriction and reconstruction below are actual continuous linear maps.
-/

namespace NoExoticSixSphere.ComplexStructureBlock

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

abbrev Space (F : Type*) := WithLp 2 (ℝ × WithLp 2 (ℝ × F))

def firstVector : Space F := WithLp.toLp 2 ((1 : ℝ), (0 : WithLp 2 (ℝ × F)))

def secondVector : Space F := WithLp.toLp 2 ((0 : ℝ), WithLp.toLp 2 ((1 : ℝ), (0 : F)))

noncomputable def tailInclusion : F →L[ℝ] Space F :=
  FixedColumnBlock.tailInclusion.comp FixedColumnBlock.tailInclusion

noncomputable def tailProjection : Space F →L[ℝ] F :=
  (WithLp.sndL 2 ℝ ℝ F).comp (WithLp.sndL 2 ℝ ℝ (WithLp 2 (ℝ × F)))

theorem tailInclusion_apply (x : F) :
    tailInclusion x = WithLp.toLp 2 ((0 : ℝ), WithLp.toLp 2 ((0 : ℝ), x)) := rfl

theorem tailProjection_apply (z : Space F) : tailProjection z = z.snd.snd := rfl

theorem tailProjection_tailInclusion (x : F) : tailProjection (tailInclusion x) = x := rfl

theorem inner_firstVector (z : Space F) : inner ℝ firstVector z = z.fst := by
  simp [firstVector, WithLp.prod_inner_apply]

theorem inner_secondVector (z : Space F) : inner ℝ secondVector z = z.snd.fst := by
  simp [secondVector, WithLp.prod_inner_apply]

theorem inner_tailInclusion (x y : F) :
    inner ℝ (tailInclusion x) (tailInclusion y) = inner ℝ x y := by
  simp [tailInclusion_apply, WithLp.prod_inner_apply]

theorem decompose (z : Space F) :
    z = z.fst • firstVector + z.snd.fst • secondVector + tailInclusion z.snd.snd := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · simp [firstVector, secondVector, tailInclusion_apply]
  · apply WithLp.ofLp_injective 2
    apply Prod.ext <;> simp [firstVector, secondVector, tailInclusion_apply]

noncomputable def tailMap (A : Space F →L[ℝ] Space F) : F →L[ℝ] F :=
  tailProjection.comp (A.comp tailInclusion)

noncomputable def block (K : F →L[ℝ] F) : Space F →L[ℝ] Space F where
  toFun z := WithLp.toLp 2 (-z.snd.fst, WithLp.toLp 2 (z.fst, K z.snd.snd))
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · simp [add_comm]
    · apply WithLp.ofLp_injective 2
      apply Prod.ext <;> simp
  map_smul' r x := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · simp
    · apply WithLp.ofLp_injective 2
      apply Prod.ext <;> simp
  cont := (WithLp.prod_continuous_toLp 2 ℝ (WithLp 2 (ℝ × F))).comp
    (((WithLp.continuous_fst 2 ℝ F).comp
      (WithLp.continuous_snd 2 ℝ (WithLp 2 (ℝ × F)))).neg.prodMk
      ((WithLp.prod_continuous_toLp 2 ℝ F).comp
        ((WithLp.continuous_fst 2 ℝ (WithLp 2 (ℝ × F))).prodMk
          (K.continuous.comp ((WithLp.continuous_snd 2 ℝ F).comp
            (WithLp.continuous_snd 2 ℝ (WithLp 2 (ℝ × F))))))))

theorem block_apply (K : F →L[ℝ] F) (z : Space F) :
    block K z = WithLp.toLp 2 (-z.snd.fst, WithLp.toLp 2 (z.fst, K z.snd.snd)) := rfl

theorem block_firstVector (K : F →L[ℝ] F) : block K firstVector = secondVector := by
  simp [block_apply, firstVector, secondVector]

theorem tailMap_block (K : F →L[ℝ] F) : tailMap (block K) = K := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

theorem block_square (K : F →L[ℝ] F) (hK : K.comp K = -(1 : F →L[ℝ] F)) :
    (block K).comp (block K) = -(1 : Space F →L[ℝ] Space F) := by
  apply ContinuousLinearMap.ext
  intro z
  have h := DFunLike.congr_fun hK z.snd.snd
  change K (K z.snd.snd) = -z.snd.snd at h
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · rfl
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · rfl
    · exact h

variable [CompleteSpace F]

theorem inner_skew (K : F →L[ℝ] F) (hK : K.adjoint = -K) (x y : F) :
    inner ℝ (K x) y = -inner ℝ x (K y) := by
  have h := K.adjoint_inner_right x y
  rw [hK] at h
  simpa only [neg_apply, inner_neg_right] using h.symm

theorem block_skew (K : F →L[ℝ] F) (hK : K.adjoint = -K) :
    (block K).adjoint = -(block K) := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (block K x) y = inner ℝ x (-(block K y))
  simp only [inner_neg_right, block_apply, WithLp.prod_inner_apply,
    WithLp.ofLp_fst, WithLp.ofLp_snd, inner_neg_left]
  rw [inner_skew K hK]
  ring

omit [CompleteSpace F] in
theorem secondVector_apply (A : Space F →L[ℝ] Space F)
    (hsq : A.comp A = -(1 : Space F →L[ℝ] Space F))
    (hcol : A firstVector = secondVector) : A secondVector = -firstVector := by
  have h := DFunLike.congr_fun hsq firstVector
  change A (A firstVector) = -firstVector at h
  rwa [hcol] at h

theorem first_apply (A : Space F →L[ℝ] Space F) (hA : A.adjoint = -A)
    (hcol : A firstVector = secondVector) (z : Space F) :
    (A z).fst = -z.snd.fst := by
  have h := inner_skew A hA firstVector z
  rw [hcol, inner_secondVector, inner_firstVector] at h
  linarith

theorem second_apply (A : Space F →L[ℝ] Space F) (hA : A.adjoint = -A)
    (hsq : A.comp A = -(1 : Space F →L[ℝ] Space F))
    (hcol : A firstVector = secondVector) (z : Space F) :
    (A z).snd.fst = z.fst := by
  have h := inner_skew A hA secondVector z
  rw [secondVector_apply A hsq hcol, inner_neg_left,
    inner_firstVector, inner_secondVector] at h
  linarith

theorem apply_tailInclusion (A : Space F →L[ℝ] Space F) (hA : A.adjoint = -A)
    (hsq : A.comp A = -(1 : Space F →L[ℝ] Space F))
    (hcol : A firstVector = secondVector) (x : F) :
    A (tailInclusion x) = tailInclusion (tailMap A x) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change (A (tailInclusion x)).fst = 0
    have h := first_apply A hA hcol (tailInclusion x)
    change (A (tailInclusion x)).fst = -(0 : ℝ) at h
    simpa only [neg_zero] using h
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · change (A (tailInclusion x)).snd.fst = 0
      exact second_apply A hA hsq hcol (tailInclusion x)
    · rfl

theorem tailMap_skew (A : Space F →L[ℝ] Space F) (hA : A.adjoint = -A)
    (hsq : A.comp A = -(1 : Space F →L[ℝ] Space F))
    (hcol : A firstVector = secondVector) : (tailMap A).adjoint = -(tailMap A) := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (tailMap A x) y = inner ℝ x (-(tailMap A y))
  rw [inner_neg_right]
  have h := inner_skew A hA (tailInclusion x) (tailInclusion y)
  rwa [apply_tailInclusion A hA hsq hcol, apply_tailInclusion A hA hsq hcol,
    inner_tailInclusion, inner_tailInclusion] at h

theorem tailMap_square (A : Space F →L[ℝ] Space F) (hA : A.adjoint = -A)
    (hsq : A.comp A = -(1 : Space F →L[ℝ] Space F))
    (hcol : A firstVector = secondVector) :
    (tailMap A).comp (tailMap A) = -(1 : F →L[ℝ] F) := by
  apply ContinuousLinearMap.ext
  intro x
  change tailMap A (tailMap A x) = -x
  have h := DFunLike.congr_fun hsq (tailInclusion x)
  change A (A (tailInclusion x)) = -tailInclusion x at h
  rw [apply_tailInclusion A hA hsq hcol, apply_tailInclusion A hA hsq hcol] at h
  have hp := congrArg (tailProjection (F := F)) h
  simpa only [tailProjection_tailInclusion, map_neg] using hp

theorem eq_block_tailMap (A : Space F →L[ℝ] Space F) (hA : A.adjoint = -A)
    (hsq : A.comp A = -(1 : Space F →L[ℝ] Space F))
    (hcol : A firstVector = secondVector) : A = block (tailMap A) := by
  apply ContinuousLinearMap.ext
  intro z
  calc
    A z = A (z.fst • firstVector + z.snd.fst • secondVector + tailInclusion z.snd.snd) :=
      congrArg A (decompose z)
    _ = z.fst • secondVector + z.snd.fst • (-firstVector) +
        tailInclusion (tailMap A z.snd.snd) := by
      rw [map_add, map_add, map_smul, map_smul, hcol,
        secondVector_apply A hsq hcol, apply_tailInclusion A hA hsq hcol]
    _ = block (tailMap A) z := by
      apply WithLp.ofLp_injective 2
      apply Prod.ext
      · simp [firstVector, secondVector, tailInclusion_apply, block_apply]
      · apply WithLp.ofLp_injective 2
        apply Prod.ext <;> simp [firstVector, secondVector, tailInclusion_apply, block_apply]

variable {X : Type*} [TopologicalSpace X]

omit [CompleteSpace F] in
theorem continuous_tailMap (A : X → Space F →L[ℝ] Space F) (hA : Continuous A) :
    Continuous (fun x ↦ tailMap (A x)) :=
  continuous_const.clm_comp (hA.clm_comp continuous_const)

omit [CompleteSpace F] in
theorem continuous_block [FiniteDimensional ℝ F] (K : X → F →L[ℝ] F)
    (hK : Continuous K) : Continuous (fun x ↦ block (K x)) := by
  apply continuous_clm_apply.mpr
  intro z
  exact (WithLp.prod_continuous_toLp 2 ℝ (WithLp 2 (ℝ × F))).comp
    (continuous_const.prodMk ((WithLp.prod_continuous_toLp 2 ℝ F).comp
      (continuous_const.prodMk (hK.clm_apply continuous_const))))

end NoExoticSixSphere.ComplexStructureBlock
