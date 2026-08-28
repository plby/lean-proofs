import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPolygonRealization

/-! # The explicit symplectic exponential on each polygon interval -/

noncomputable section

open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open VertexSpace Exponential

variable {n m : ℕ}

def rescaledSegment (a : symplecticSubgroup n) (K : SkewSpace n)
    (s u t : ℝ) : symplecticSubgroup n :=
  a * exp (((t - s) / (u - s)) • K)

theorem rescaledSegment_forget (a : symplecticSubgroup n) (K : SkewSpace n)
    (s u t : ℝ) :
    (rescaledSegment a K s u t).val =
      NoExoticSixSphere.OrthogonalPathEnergy.rescaledSegment
        a.val (toOrthogonalSkew n K) s u t := by
  change a.val * NoExoticSixSphere.OrthogonalExponential.exp
    (toOrthogonalSkew n (((t - s) / (u - s)) • K)) = _
  rw [map_smul]
  rfl

theorem path_eq_segment (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) {v : Space n m} (hv : v ∈ admissible a b m)
    (i : Fin (m + 1)) {t : ℝ} (ht : t ∈ Icc (τ i.castSucc) (τ i.succ)) :
    path a b τ v t = rescaledSegment (vertices a b v i.castSucc)
      (generator a b v i) (τ i.castSucc) (τ i.succ) t := by
  apply Subtype.ext
  rw [path_forget a b τ hv, rescaledSegment_forget, vertices_forget,
    ← generator_forget a b hv i]
  exact NoExoticSixSphere.OrthogonalPolygon.path_eq_segment a.val b.val τ hτ
    (admissible_forget a b hv) i ht

theorem rescaledSegment_increment (a : symplecticSubgroup n) (K : SkewSpace n)
    (s u α β : ℝ) :
    (rescaledSegment a K s u α)⁻¹ * rescaledSegment a K s u β =
      exp (((β - α) / (u - s)) • K) := by
  apply mul_left_cancel (a := rescaledSegment a K s u α)
  rw [mul_inv_cancel_left]
  simp only [rescaledSegment, mul_assoc, ← exp_add_smul]
  apply congrArg (fun r : ℝ ↦ a * exp (r • K))
  ring

theorem rescaledSegment_subsegment (a : symplecticSubgroup n) (K : SkewSpace n)
    (s u α β t : ℝ) (hαβ : α ≠ β) :
    rescaledSegment (rescaledSegment a K s u α) (((β - α) / (u - s)) • K) α β t =
      rescaledSegment a K s u t := by
  simp only [rescaledSegment, smul_smul, mul_assoc, ← exp_add_smul]
  apply congrArg (fun r : ℝ ↦ a * exp (r • K))
  have hd : β - α ≠ 0 := sub_ne_zero.mpr hαβ.symm
  calc
    (α - s) / (u - s) + (t - α) / (β - α) * ((β - α) / (u - s)) =
        (α - s) / (u - s) + (t - α) / (u - s) := by
      rw [div_mul_div_cancel₀ hd]
    _ = (t - s) / (u - s) := by ring

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon
