import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicVertexSpace

/-! # Joint continuous Cayley interpolation between nearby symplectic vertex lists -/

noncomputable section

open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.VertexSpace

variable {n m : ℕ}

private theorem real_smul_zero {V : Type*} [AddCommGroup V] [Module ℝ V] (t : ℝ) :
    t • (0 : V) = 0 := smul_zero t

def interpolationDomain (n m : ℕ) : Set (Space n m × Space n m) :=
  {p | ∀ i, (p.1 i)⁻¹ * p.2 i ∈ cayleyDomain n}

theorem isOpen_interpolationDomain (n m : ℕ) : IsOpen (interpolationDomain n m) := by
  change IsOpen {p : Space n m × Space n m | ∀ i, (p.1 i)⁻¹ * p.2 i ∈ cayleyDomain n}
  rw [ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact (isOpen_cayleyDomain n).preimage
    (((continuous_apply i).comp continuous_fst).inv.mul ((continuous_apply i).comp continuous_snd))

theorem diagonal_mem_interpolationDomain (v : Space n m) :
    (v, v) ∈ interpolationDomain n m := by
  intro i
  rw [inv_mul_cancel]
  exact one_mem_cayleyDomain n

def interpolate (t : ℝ) (v w : Space n m) : Space n m :=
  fun i => v i * symplecticCayley n (t • cayleyCoordinates n ((v i)⁻¹ * w i))

theorem interpolate_zero (v w : Space n m) : interpolate 0 v w = v := by
  funext i
  rw [interpolate, zero_smul, symplecticCayley_zero]
  exact mul_one (v i)

theorem interpolate_one (v w : Space n m) (h : (v, w) ∈ interpolationDomain n m) :
    interpolate 1 v w = w := by
  funext i
  have hc : symplecticCayley n (cayleyCoordinates n ((v i)⁻¹ * w i)) = (v i)⁻¹ * w i :=
    (cayleyChart n).left_inv (h i)
  rw [interpolate, one_smul, hc, mul_inv_cancel_left]

theorem interpolate_self (t : ℝ) (v : Space n m) : interpolate t v v = v := by
  funext i
  have hc : cayleyCoordinates n (1 : symplecticSubgroup n) = 0 := cayleyChart_one n
  rw [interpolate, inv_mul_cancel, hc, real_smul_zero (V := SkewSpace n) t,
    symplecticCayley_zero]
  exact mul_one (v i)

theorem continuous_interpolate {X : Type*} [TopologicalSpace X]
    (p q : X → Space n m) (hp : Continuous p) (hq : Continuous q)
    (hpair : ∀ x, (p x, q x) ∈ interpolationDomain n m) :
    Continuous (fun z : ℝ × X => interpolate z.1 (p z.2) (q z.2)) := by
  apply continuous_pi
  intro i
  have hr : Continuous (fun x => (p x i)⁻¹ * q x i) :=
    ((continuous_apply i).comp hp).inv.mul ((continuous_apply i).comp hq)
  have hc : Continuous (fun x => cayleyCoordinates n ((p x i)⁻¹ * q x i)) :=
    (cayleyChart n).continuousOn_toFun.comp_continuous hr (fun x => hpair x i)
  have hscale : Continuous (fun z : ℝ × X => z.1 • cayleyCoordinates n ((p z.2 i)⁻¹ * q z.2 i)) :=
    continuous_fst.smul (hc.comp continuous_snd)
  exact (((continuous_apply i).comp hp).comp continuous_snd).mul
    ((continuous_symplecticCayley n).comp hscale)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.VertexSpace
