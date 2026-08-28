import Wikipedia.NoExoticSixSphere.OutwardGraphFrame

/-!
# Actual continuous homotopies to the outward boundary operator

First graph the time covector on the derivative columns, while the added
normal remains the height axis. Then move that normal to the outward
vector. Both families remain injective and preserve all original normal
columns. The final operator is the exact combined operator of the full
boundary normal frame and the time-graph derivative.
-/

noncomputable section

open Function unitInterval

namespace NoExoticSixSphere.OutwardGraphFrame

open GLOrthonormalization Stiefel CollaredDiskFrame

variable {N k : ℕ} {X : Type*} [TopologicalSpace X]
  (A : C(X, Vector k →L[ℝ] Vector N)) (D : C(X, Vector 4 →L[ℝ] Vector N))
  (ν : C(X, Vector N)) (ξ : C(X, Vector N →L[ℝ] ℝ))
  (hAD : ∀ x, Injective ((A x).coprod (D x)))
  (hA : ∀ x u, ξ x (A x u) = 0) (hν : ∀ x, ξ x (ν x) < 0)

def heightFamily (p : I × X) : Vector (((k + 1) + 5) + 4) →L[ℝ] Vector (N + 6) :=
  combined (normal 0 (A p.2) (ν p.2)) (graph (D p.2) ((p.1 : ℝ) • ξ p.2))

include hAD hA in
theorem heightFamily_injective (p : I × X) : Injective (heightFamily A D ν ξ p) := by
  apply combined_injective_of_coprod
  apply coprod_injective_of_coefficient 0 _ _ _ _ (hAD p.2)
  · intro u
    change (p.1 : ℝ) * ξ p.2 (A p.2 u) = 0
    rw [hA, mul_zero]
  · simp only [sub_zero, zero_mul, add_zero]
    norm_num

theorem continuous_heightFamily : Continuous (heightFamily A D ν ξ) := by
  have ht : Continuous (fun p : I × X ↦ (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  exact continuous_combined _ _
    (continuous_normal _ _ _ continuous_const
      (A.continuous.comp continuous_snd) (ν.continuous.comp continuous_snd))
    (continuous_graph _ _ (D.continuous.comp continuous_snd)
      (ht.smul (ξ.continuous.comp continuous_snd)))

def outwardFamily (p : I × X) : Vector (((k + 1) + 5) + 4) →L[ℝ] Vector (N + 6) :=
  combined (normal (p.1 : ℝ) (A p.2) (ν p.2)) (graph (D p.2) (ξ p.2))

include hAD hA hν in
theorem outwardFamily_injective (p : I × X) : Injective (outwardFamily A D ν ξ p) :=
  combined_injective_of_coprod _ _
    (coprod_injective p.1 p.1.property (A p.2) (D p.2) (ν p.2) (ξ p.2)
      (hAD p.2) (hA p.2) (hν p.2))

theorem continuous_outwardFamily : Continuous (outwardFamily A D ν ξ) :=
  continuous_combined _ _
    (continuous_normal _ _ _ (continuous_subtype_val.comp continuous_fst)
      (A.continuous.comp continuous_snd) (ν.continuous.comp continuous_snd))
    (continuous_graph _ _ (D.continuous.comp continuous_snd)
      (ξ.continuous.comp continuous_snd))

include hAD hA hν in
theorem homotopic_plain_to_outward
    (F G : C(X, Monomorphism.Space (N + 6) (((k + 1) + 5) + 4)))
    (hF : ∀ x, (F x).val = combined (normal 0 (A x) (ν x)) (graph (D x) 0))
    (hG : ∀ x, (G x).val =
      combined ((ContinuousLinearMap.inl ℝ (Vector N) ℝ).comp
        (OrthogonalFrameAppend.operator (A x) (ν x))) (graph (D x) (ξ x))) :
    F.Homotopic G := by
  let H : C(X, Monomorphism.Space (N + 6) (((k + 1) + 5) + 4)) := {
    toFun x := ⟨outwardFamily A D ν ξ (0, x),
      outwardFamily_injective A D ν ξ hAD hA hν (0, x)⟩
    continuous_toFun := ((continuous_outwardFamily A D ν ξ).comp
      (continuous_const.prodMk continuous_id)).subtype_mk _ }
  have hFH : F.Homotopic H := by
    refine ⟨{
      toFun := fun p ↦ ⟨heightFamily A D ν ξ p, heightFamily_injective A D ν ξ hAD hA p⟩
      continuous_toFun := (continuous_heightFamily A D ν ξ).subtype_mk _
      map_zero_left := ?_
      map_one_left := ?_ }⟩
    · intro x
      apply Subtype.ext
      change combined _ (graph _ ((0 : ℝ) • ξ x)) = (F x).val
      rw [zero_smul]
      exact (hF x).symm
    · intro x
      apply Subtype.ext
      change combined _ (graph _ ((1 : ℝ) • ξ x)) =
        combined (normal 0 (A x) (ν x)) (graph (D x) (ξ x))
      rw [one_smul]
  have hHG : H.Homotopic G := by
    refine ⟨{
      toFun := fun p ↦ ⟨outwardFamily A D ν ξ p,
        outwardFamily_injective A D ν ξ hAD hA hν p⟩
      continuous_toFun := (continuous_outwardFamily A D ν ξ).subtype_mk _
      map_zero_left := ?_
      map_one_left := ?_ }⟩
    · intro x
      rfl
    · intro x
      apply Subtype.ext
      change combined (normal 1 (A x) (ν x)) (graph (D x) (ξ x)) = (G x).val
      rw [normal_one]
      exact (hG x).symm
  exact hFH.trans hHG

end NoExoticSixSphere.OutwardGraphFrame
