import Wikipedia.HopfProblem.DegreeCollapseCylindricalCoordinates

/-!
# Ordered Euclidean coordinates for adjoining a real normal line

The new coordinate is first and the original Euclidean coordinates are
unchanged in the tail. The Hilbert product identification is an actual
linear isometry, with explicit coordinate and inner-product formulas.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.EuclideanProduct

open CylindricalTube

abbrev Vector (n : ℕ) := EuclideanSpace ℝ (Fin n)

def headLinearEquiv (n : ℕ) : Normal (Vector n) ≃ₗ[ℝ] Vector (n + 1) where
  toFun w := WithLp.toLp 2 (Fin.cons w.fst (fun i ↦ w.snd i))
  invFun v := WithLp.toLp 2 (v 0, WithLp.toLp 2 (fun i : Fin n ↦ v i.succ))
  left_inv w := by
    apply WithLp.ofLp_injective
    refine Prod.ext rfl ?_
    ext i
    rfl
  right_inv v := by
    ext i
    exact Fin.cases rfl (fun _ ↦ rfl) i
  map_add' w z := by
    ext i
    exact Fin.cases rfl (fun _ ↦ rfl) i
  map_smul' c w := by
    ext i
    exact Fin.cases rfl (fun _ ↦ rfl) i

theorem headLinearEquiv_norm (n : ℕ) (w : Normal (Vector n)) :
    ‖headLinearEquiv n w‖ = ‖w‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  change w.fst ^ 2 + ∑ i : Fin n, (w.snd i) ^ 2 = ‖w‖ ^ 2
  rw [← EuclideanSpace.real_norm_sq_eq, WithLp.prod_norm_sq_eq_of_L2,
    Real.norm_eq_abs, sq_abs]

def headIsometry (n : ℕ) : Normal (Vector n) ≃ₗᵢ[ℝ] Vector (n + 1) where
  toLinearEquiv := headLinearEquiv n
  norm_map' := headLinearEquiv_norm n

def coordinates (n : ℕ) : (ℝ × Vector n) ≃L[ℝ] Vector (n + 1) :=
  (split (K := Vector n)).symm.trans (headIsometry n).toContinuousLinearEquiv

@[simp] theorem coordinates_head (n : ℕ) (p : ℝ × Vector n) : coordinates n p 0 = p.1 := rfl

@[simp] theorem coordinates_tail (n : ℕ) (p : ℝ × Vector n) (i : Fin n) :
    coordinates n p i.succ = p.2 i := rfl

theorem coordinates_inner (n : ℕ) (p q : ℝ × Vector n) :
    inner ℝ (coordinates n p) (coordinates n q) = p.1 * q.1 + inner ℝ p.2 q.2 := by
  change inner ℝ (headIsometry n (WithLp.toLp 2 p))
    (headIsometry n (WithLp.toLp 2 q)) = _
  rw [(headIsometry n).inner_map_map, WithLp.prod_inner_apply, Real.inner_apply]

end Wikipedia.HopfProblem.DegreeCollapse.EuclideanProduct
