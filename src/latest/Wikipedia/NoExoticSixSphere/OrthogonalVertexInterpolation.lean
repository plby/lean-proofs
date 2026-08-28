import Wikipedia.NoExoticSixSphere.OrthogonalVertexSpace

/-!
# Continuous interpolation between nearby orthogonal vertex lists

Each vertex ratio is expressed in the identity Cayley chart and its coordinate
is multiplied by the time parameter. Continuity is joint in the two lists and
time on the stated open pair domain. The interpolation fixes the diagonal.
-/

open Set

namespace NoExoticSixSphere.OrthogonalVertexSpace

open GLOrthonormalization CayleyTransform

variable {n m : ℕ}

def interpolationDomain (n m : ℕ) : Set (Space n m × Space n m) :=
  {p | ∀ i, (p.1 i)⁻¹ * p.2 i ∈ CayleyTransform.domain}

theorem isOpen_interpolationDomain (n m : ℕ) : IsOpen (interpolationDomain n m) := by
  change IsOpen {p : Space n m × Space n m | ∀ i, (p.1 i)⁻¹ * p.2 i ∈ CayleyTransform.domain}
  rw [ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact CayleyTransform.isOpen_domain.preimage
    (((continuous_apply i).comp continuous_fst).inv.mul ((continuous_apply i).comp continuous_snd))

theorem diagonal_mem_interpolationDomain (v : Space n m) :
    (v, v) ∈ interpolationDomain n m := by
  intro i
  rw [inv_mul_cancel]
  exact CayleyTransform.identity_mem_domain

noncomputable def interpolate (t : ℝ) (v w : Space n m) : Space n m :=
  fun i ↦ v i * orthogonal (t • coordinates ((v i)⁻¹ * w i))

theorem interpolate_zero (v w : Space n m) : interpolate 0 v w = v := by
  funext i
  rw [interpolate, zero_smul, orthogonal_zero]
  exact mul_one (v i)

theorem interpolate_one (v w : Space n m) (h : (v, w) ∈ interpolationDomain n m) :
    interpolate 1 v w = w := by
  funext i
  have hc : orthogonal (coordinates ((v i)⁻¹ * w i)) = (v i)⁻¹ * w i :=
    CayleyTransform.chart.left_inv (h i)
  rw [interpolate, one_smul, hc, mul_inv_cancel_left]

theorem interpolate_self (t : ℝ) (v : Space n m) : interpolate t v v = v := by
  funext i
  have hc : coordinates (1 : OrthogonalOperators n) = 0 := CayleyTransform.chart_identity
  rw [interpolate, inv_mul_cancel, hc, smul_zero, orthogonal_zero]
  exact mul_one (v i)

theorem continuous_interpolate {X : Type*} [TopologicalSpace X]
    (p q : X → Space n m) (hp : Continuous p) (hq : Continuous q)
    (hpair : ∀ x, (p x, q x) ∈ interpolationDomain n m) :
    Continuous (fun z : ℝ × X ↦ interpolate z.1 (p z.2) (q z.2)) := by
  apply continuous_pi
  intro i
  have hr : Continuous (fun x ↦ (p x i)⁻¹ * q x i) :=
    ((continuous_apply i).comp hp).inv.mul ((continuous_apply i).comp hq)
  have hc : Continuous (fun x ↦ coordinates ((p x i)⁻¹ * q x i)) := by
    have h := continuous_coordinate (fun x ↦ (p x i)⁻¹ * q x i) hr (fun x ↦ hpair x i)
    exact h.congr (fun x ↦ (coordinates_of_mem _ (hpair x i)).symm)
  have hscale : Continuous (fun z : ℝ × X ↦ z.1 • coordinates ((p z.2 i)⁻¹ * q z.2 i)) :=
    continuous_fst.smul (hc.comp continuous_snd)
  exact (((continuous_apply i).comp hp).comp continuous_snd).mul
    (continuous_orthogonal.comp hscale)

end NoExoticSixSphere.OrthogonalVertexSpace
