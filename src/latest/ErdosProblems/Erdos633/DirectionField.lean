import ErdosProblems.Erdos633.WeightedBoundary
import ErdosProblems.Erdos633.CharacterBoundary

/-!
# Propagating a coefficient field through a triangular dissection

An unoriented angle determines the quotient of two unit directions up to
inversion. A subfield containing that angle's rotation therefore transfers
membership between the two directions. Weighted boundary propagation then
puts every tile direction in the field from the outer boundary directions.
No edge-to-edge or adjacency-connectivity assumption is made.
-/

namespace Erdos633

theorem unit_ratio_eq_exp_angle_or_inv {x y : ℂ} {θ : ℝ}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hangle : InnerProductGeometry.angle x y = θ) :
    Complex.exp ((θ : ℂ) * Complex.I) = x / y ∨
      (Complex.exp ((θ : ℂ) * Complex.I))⁻¹ = x / y := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hy0 : y ≠ 0 := by intro h; simp [h] at hy
  have hn : ‖x / y‖ = 1 := by rw [norm_div, hx, hy, div_one]
  have he : Complex.exp (((x / y).arg : ℂ) * Complex.I) = x / y := by
    simpa only [hn, Complex.ofReal_one, one_mul] using
      Complex.norm_mul_exp_arg_mul_I (x / y)
  have ha : |(x / y).arg| = θ :=
    (Complex.angle_eq_abs_arg hx0 hy0).symm.trans hangle
  by_cases harg : 0 ≤ (x / y).arg
  · rw [abs_of_nonneg harg] at ha
    exact Or.inl (by rw [← ha]; exact he)
  · rw [abs_of_neg (lt_of_not_ge harg)] at ha
    have hneg : (x / y).arg = -θ := by linarith
    rw [hneg, Complex.ofReal_neg, neg_mul, Complex.exp_neg] at he
    exact Or.inr he

theorem unit_mem_subfield_of_angle (K : Subfield ℂ) {x y : ℂ} {θ : ℝ}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hangle : InnerProductGeometry.angle x y = θ)
    (hθ : Complex.exp ((θ : ℂ) * Complex.I) ∈ K) (hyK : y ∈ K) : x ∈ K := by
  have hy0 : y ≠ 0 := by intro h; simp [h] at hy
  have hratio : x / y ∈ K := by
    rcases unit_ratio_eq_exp_angle_or_inv hx hy hangle with h | h
    · rw [← h]
      exact hθ
    · rw [← h]
      exact K.inv_mem hθ
  simpa only [div_mul_cancel₀ _ hy0] using K.mul_mem hratio hyK

theorem unit_mem_subfield_iff_of_angle (K : Subfield ℂ) {x y : ℂ} {θ : ℝ}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hangle : InnerProductGeometry.angle x y = θ)
    (hθ : Complex.exp ((θ : ℂ) * Complex.I) ∈ K) : x ∈ K ↔ y ∈ K := by
  constructor
  · exact unit_mem_subfield_of_angle K hy hx
      ((InnerProductGeometry.angle_comm y x).trans hangle) hθ
  · exact unit_mem_subfield_of_angle K hx hy hangle hθ

theorem Triangle.unitEdgeVector_mem_of_one (P : Triangle) (K : Subfield ℂ)
    (hA : Complex.exp ((P.angleA : ℂ) * Complex.I) ∈ K)
    (hB : Complex.exp ((P.angleB : ℂ) * Complex.I) ∈ K)
    (l : Fin 3) (hl : P.unitEdgeVector l ∈ K) :
    ∀ k : Fin 3, P.unitEdgeVector k ∈ K := by
  have h0 : P.unitEdgeVector 0 ∈ K ↔ P.unitEdgeVector 2 ∈ K := by
    have h := unit_mem_subfield_iff_of_angle K (P.norm_unitEdgeVector 0)
      (by rw [norm_neg, P.norm_unitEdgeVector]) P.angle_unitEdge_zero_neg_two hB
    exact h.trans ⟨fun h => by simpa only [neg_neg] using K.neg_mem h,
      fun h => K.neg_mem h⟩
  have h1 : P.unitEdgeVector 1 ∈ K ↔ P.unitEdgeVector 2 ∈ K := by
    have h := unit_mem_subfield_iff_of_angle K (P.norm_unitEdgeVector 1)
      (by rw [norm_neg, P.norm_unitEdgeVector]) P.angle_unitEdge_one_neg_two hA
    exact h.trans ⟨fun h => by simpa only [neg_neg] using K.neg_mem h,
      fun h => K.neg_mem h⟩
  have h2 : P.unitEdgeVector 2 ∈ K := by
    fin_cases l
    · exact h0.mp hl
    · exact h1.mp hl
    · exact hl
  intro k
  fin_cases k
  · exact h0.mpr h2
  · exact h1.mpr h2
  · exact h2

theorem TriangleDissection.unitEdgeVectors_mem_subfield
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N) (K : Subfield ℂ)
    (houter : ∀ k : Fin 3, P.unitEdgeVector k ∈ K)
    (hA : ∀ i : Fin N, Complex.exp (((T.tile i).angleA : ℂ) * Complex.I) ∈ K)
    (hB : ∀ i : Fin N, Complex.exp (((T.tile i).angleB : ℂ) * Complex.I) ∈ K) :
    ∀ i : Fin N, ∀ k : Fin 3, (T.tile i).unitEdgeVector k ∈ K := by
  apply T.property_of_boundary_and_shared (fun i => ∀ k, (T.tile i).unitEdgeVector k ∈ K)
  · intro i k l hl
    apply (T.tile i).unitEdgeVector_mem_of_one K (hA i) (hB i) l
    rw [P.unitEdgeVector_eq_of_edge_subset (T.tile i) k l (T.tile_subset i) hl]
    exact houter k
  · intro i j hij k l z hi hj hp
    apply (T.tile j).unitEdgeVector_mem_of_one K (hA j) (hB j) l
    rw [T.shared_open_edges_unitVector_neg hij k l hi hj]
    exact K.neg_mem (hp k)

theorem CongruentTiling.labelled_unitEdgeVectors_mem_subfield
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) (K : Subfield ℂ)
    (houter : ∀ k : Fin 3, P.unitEdgeVector k ∈ K)
    (hA : Complex.exp ((R.angleA : ℂ) * Complex.I) ∈ K)
    (hB : Complex.exp ((R.angleB : ℂ) * Complex.I) ∈ K) :
    ∀ i : Fin N, ∀ k : Fin 3, (T.labelledTile i).unitEdgeVector k ∈ K := by
  apply T.labelledDissection.unitEdgeVectors_mem_subfield K houter
  · intro i
    have ha : (T.labelledTile i).angleA = R.angleA := by
      simpa [Triangle.cornerAngle] using T.labelledTile_cornerAngle i 0
    change Complex.exp (((T.labelledTile i).angleA : ℂ) * Complex.I) ∈ K
    rwa [ha]
  · intro i
    have hb : (T.labelledTile i).angleB = R.angleB := by
      simpa [Triangle.cornerAngle] using T.labelledTile_cornerAngle i 1
    change Complex.exp (((T.labelledTile i).angleB : ℂ) * Complex.I) ∈ K
    rwa [hb]

theorem exp_nat_angle_sum_mem_subfield {ι : Type*} (K : Subfield ℂ)
    (s : Finset ι) (n : ι → ℕ) (θ : ι → ℝ)
    (hθ : ∀ j ∈ s, Complex.exp ((θ j : ℂ) * Complex.I) ∈ K) :
    Complex.exp (((∑ j ∈ s, (n j : ℝ) * θ j : ℝ) : ℂ) * Complex.I) ∈ K := by
  have heq : ((∑ j ∈ s, (n j : ℝ) * θ j : ℝ) : ℂ) * Complex.I =
      ∑ j ∈ s, (n j : ℂ) * ((θ j : ℂ) * Complex.I) := by
    push_cast
    rw [Finset.sum_mul]
    simp only [mul_assoc]
  rw [heq, Complex.exp_sum]
  apply K.prod_mem
  intro j hj
  rw [Complex.exp_nat_mul]
  exact K.pow_mem (hθ j hj) (n j)

theorem Triangle.angleC_rotation_mem_subfield (P : Triangle) (K : Subfield ℂ)
    (hA : Complex.exp ((P.angleA : ℂ) * Complex.I) ∈ K)
    (hB : Complex.exp ((P.angleB : ℂ) * Complex.I) ∈ K) :
    Complex.exp ((P.angleC : ℂ) * Complex.I) ∈ K := by
  have heq : P.angleC = Real.pi - P.angleA - P.angleB := by linarith [P.angle_sum]
  rw [heq, Complex.ofReal_sub, Complex.ofReal_sub, sub_mul, sub_mul,
    Complex.exp_sub, Complex.exp_sub, Complex.exp_pi_mul_I]
  exact K.div_mem (K.div_mem (K.neg_mem K.one_mem) hA) hB

theorem CongruentTiling.outer_rotation_mem_subfield
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) (K : Subfield ℂ)
    (hA : Complex.exp ((R.angleA : ℂ) * Complex.I) ∈ K)
    (hB : Complex.exp ((R.angleB : ℂ) * Complex.I) ∈ K) (j : Fin 3) :
    Complex.exp ((P.cornerAngle j : ℂ) * Complex.I) ∈ K := by
  rw [← T.outer_angle_count_identity j]
  apply exp_nat_angle_sum_mem_subfield K Finset.univ
  intro k _
  fin_cases k
  · simpa [Triangle.cornerAngle] using hA
  · simpa [Triangle.cornerAngle] using hB
  · simpa [Triangle.cornerAngle] using R.angleC_rotation_mem_subfield K hA hB

/-- A single outer direction and the two reference rotations generate all
counterclockwise tile directions in an actual congruent tiling. -/
theorem CongruentTiling.labelled_unitEdgeVectors_mem_of_base
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) (K : Subfield ℂ)
    (hbase : P.unitEdgeVector 2 ∈ K)
    (hA : Complex.exp ((R.angleA : ℂ) * Complex.I) ∈ K)
    (hB : Complex.exp ((R.angleB : ℂ) * Complex.I) ∈ K) :
    ∀ i : Fin N, ∀ k : Fin 3, (T.labelledTile i).unitEdgeVector k ∈ K := by
  apply T.labelled_unitEdgeVectors_mem_subfield K _ hA hB
  apply P.unitEdgeVector_mem_of_one K _ _ 2 hbase
  · simpa [Triangle.cornerAngle] using T.outer_rotation_mem_subfield K hA hB 0
  · simpa [Triangle.cornerAngle] using T.outer_rotation_mem_subfield K hA hB 1

end Erdos633
