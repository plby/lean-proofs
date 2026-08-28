import Wikipedia.NoExoticSixSphere.CollaredDiskRadialOperator

/-!
# Straightening a genuine collared boundary operator

Keep the prescribed normal and tangent columns. Remove the spatial part
of the radial column and interpolate its positive height coefficient to
two. The combined operators remain injective. The endpoint is exactly
the existing source-twisted stabilized sphere operator, not an assigned
homotopy class and not an untwisted replacement.
-/

noncomputable section

open Function unitInterval

namespace NoExoticSixSphere.CollaredDiskFrame

open GLOrthonormalization Stiefel SpanningDiskFrameCoordinates SphereThreeTangentFrame

variable {N k : ℕ}
  (a : C(Sphere 3, Vector k →L[ℝ] Vector N))
  (T : C(Sphere 3, Vector 3 →L[ℝ] Vector N))
  (v : C(Sphere 3, Vector N)) (c : C(Sphere 3, ℝ))
  (ha : ∀ s, Injective (a s)) (hT : ∀ s, Injective (T s))
  (hr : ∀ s, Disjoint (a s).range (T s).range) (hc : ∀ s, 0 < c s)

def collarHeight (p : I × Sphere 3) : ℝ :=
  (1 - (p.1 : ℝ)) * c p.2 + (p.1 : ℝ) * 2

include hc in
theorem collarHeight_pos (p : I × Sphere 3) : 0 < collarHeight c p := by
  have h := (convex_Ioi (𝕜 := ℝ) (0 : ℝ)) (hc p.2)
    (show (0 : ℝ) < 2 by norm_num) (sub_nonneg.mpr p.1.property.2) p.1.property.1
    (show (1 - (p.1 : ℝ)) + (p.1 : ℝ) = 1 by ring)
  simpa only [collarHeight, smul_eq_mul, Set.mem_Ioi] using h

def sphereOperatorMap : C(Sphere 3, Monomorphism.Space N (k + 3)) where
  toFun s := ⟨OperatorSum.operator (a s) (T s),
    OperatorSum.injective_operator _ _ (ha s) (hT s) (hr s)⟩
  continuous_toFun := (OperatorSum.continuous_operator _ _ a.continuous T.continuous).subtype_mk _

def collarFamily (p : I × Sphere 3) : Vector ((k + 5) + 4) →L[ℝ] Vector (N + 6) :=
  combined ((ContinuousLinearMap.inl ℝ (Vector N) ℝ).comp (a p.2))
    (collarDerivative p.2 (T p.2) ((1 - (p.1 : ℝ)) • v p.2) (collarHeight c p))

include ha hT hr hc in
theorem collarFamily_injective (p : I × Sphere 3) : Injective (collarFamily a T v c p) :=
  combined_injective_of_coprod _ _
    (collar_coprod_injective p.2 (a p.2) (T p.2) _ _ (ha p.2) (hT p.2) (hr p.2)
      (collarHeight_pos c hc p).ne')

theorem continuous_collarFamily : Continuous (collarFamily a T v c) := by
  have ht : Continuous (fun p : I × Sphere 3 ↦ (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hheight : Continuous (collarHeight c) :=
    ((continuous_const.sub ht).mul (c.continuous.comp continuous_snd)).add
      (ht.mul continuous_const)
  exact continuous_combined _ _
    (continuous_const.clm_comp (a.continuous.comp continuous_snd))
    (continuous_collarDerivative _ _ _ _ continuous_snd (T.continuous.comp continuous_snd)
      ((continuous_const.sub ht).smul (v.continuous.comp continuous_snd)) hheight)

theorem collarFamily_zero (s : Sphere 3) :
    collarFamily a T v c (0, s) =
      combined ((ContinuousLinearMap.inl ℝ (Vector N) ℝ).comp (a s))
        (collarDerivative s (T s) (v s) (c s)) := by
  change combined _ (collarDerivative s (T s) ((1 - (0 : ℝ)) • v s)
    ((1 - (0 : ℝ)) * c s + (0 : ℝ) * 2)) = _
  rw [sub_zero, one_smul, one_mul, zero_mul, add_zero]

theorem collarFamily_one (s : Sphere 3) :
    collarFamily a T v c (1, s) =
      (twistedBlockMap (sphereOperatorMap a T ha hT hr) s).val := by
  change combined ((ContinuousLinearMap.inl ℝ (Vector N) ℝ).comp (a s))
    (collarDerivative s (T s) ((1 - (1 : ℝ)) • v s)
      ((1 - (1 : ℝ)) * c s + (1 : ℝ) * 2)) = _
  rw [sub_self, zero_smul, zero_mul, one_mul, zero_add, twistedBlockMap_value]
  apply calibrated_factorization
  intro z
  rw [collarDerivative_radialCoordinates, smul_zero, add_zero, mul_comm]

def collarMap : C(Sphere 3, Monomorphism.Space (N + 6) ((k + 5) + 4)) where
  toFun s := ⟨combined ((ContinuousLinearMap.inl ℝ (Vector N) ℝ).comp (a s))
      (collarDerivative s (T s) (v s) (c s)),
    combined_injective_of_coprod _ _
      (collar_coprod_injective s (a s) (T s) (v s) (c s) (ha s) (hT s) (hr s) (hc s).ne')⟩
  continuous_toFun := (continuous_combined _ _
    (continuous_const.clm_comp a.continuous)
    (continuous_collarDerivative _ _ _ _ continuous_id T.continuous v.continuous
      c.continuous)).subtype_mk _

def collarHomotopy :
    (collarMap a T v c ha hT hr hc).Homotopy
      (twistedBlockMap (sphereOperatorMap a T ha hT hr)) where
  toFun p := ⟨collarFamily a T v c p, collarFamily_injective a T v c ha hT hr hc p⟩
  continuous_toFun := (continuous_collarFamily a T v c).subtype_mk _
  map_zero_left s := Subtype.ext (collarFamily_zero a T v c s)
  map_one_left s := Subtype.ext (collarFamily_one a T v c ha hT hr s)

end NoExoticSixSphere.CollaredDiskFrame
