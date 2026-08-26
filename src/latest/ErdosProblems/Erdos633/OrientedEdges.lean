import ErdosProblems.Erdos633.SharedEdgeGeometry

/-!
# Counterclockwise edge directions and local cancellation

Each triangle is oriented counterclockwise independently of its vertex labels.
At a shared open edge, the two normalized directed edge vectors are negatives.
-/

namespace Erdos633

noncomputable def Triangle.orientationSign (P : Triangle) : ℝ :=
  if 0 < orientedDoubleArea P.a P.b P.c then 1 else -1

def Triangle.edgeVector (P : Triangle) (k : Fin 3) : ℂ := P.edgeEnd k - P.edgeStart k

noncomputable def Triangle.orientedEdgeVector (P : Triangle) (k : Fin 3) : ℂ :=
  P.orientationSign • P.edgeVector k

noncomputable def Triangle.unitEdgeVector (P : Triangle) (k : Fin 3) : ℂ :=
  (P.sideLength k)⁻¹ • P.orientedEdgeVector k

theorem Triangle.orientationSign_mul_self (P : Triangle) :
    P.orientationSign * P.orientationSign = 1 := by
  unfold Triangle.orientationSign
  split_ifs <;> norm_num

theorem Triangle.orientationSign_area_pos (P : Triangle) :
    0 < P.orientationSign * orientedDoubleArea P.a P.b P.c := by
  unfold Triangle.orientationSign
  split_ifs with h
  · simpa using h
  · have hn : orientedDoubleArea P.a P.b P.c < 0 :=
      lt_of_le_of_ne (le_of_not_gt h) P.nondegenerate
    simpa using neg_pos.mpr hn

theorem Triangle.edgeVector_ne_zero (P : Triangle) (k : Fin 3) : P.edgeVector k ≠ 0 :=
  sub_ne_zero.mpr (P.edgeStart_ne_edgeEnd k).symm

theorem Triangle.norm_edgeVector (P : Triangle) (k : Fin 3) :
    ‖P.edgeVector k‖ = P.sideLength k := by
  rw [Triangle.edgeVector, Triangle.sideLength, dist_comm, dist_eq_norm]

theorem Triangle.norm_orientedEdgeVector (P : Triangle) (k : Fin 3) :
    ‖P.orientedEdgeVector k‖ = P.sideLength k := by
  rw [Triangle.orientedEdgeVector, norm_smul, P.norm_edgeVector]
  unfold Triangle.orientationSign
  split_ifs <;> simp

theorem Triangle.norm_unitEdgeVector (P : Triangle) (k : Fin 3) :
    ‖P.unitEdgeVector k‖ = 1 := by
  rw [Triangle.unitEdgeVector, norm_smul, P.norm_orientedEdgeVector,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (P.sideLength_pos k)),
    inv_mul_cancel₀ (ne_of_gt (P.sideLength_pos k))]

theorem Triangle.orientedDoubleArea_edge (P : Triangle) (k : Fin 3) (z : ℂ) :
    orientedDoubleArea (P.edgeStart k) (P.edgeEnd k) z =
      orientedDoubleArea P.a P.b P.c * P.barycentric z k := by
  have h (w : ℂ) :
      orientedDoubleArea (P.edgeStart k) (P.edgeEnd k) (P.coordinateEquiv w) =
        orientedDoubleArea P.a P.b P.c * ![1 - w.re - w.im, w.re, w.im] k := by
    have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk with rfl | rfl | rfl <;>
      simp only [Triangle.edgeStart, Triangle.edgeEnd, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        Triangle.coordinateEquiv_apply,
        orientedDoubleArea, Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.smul_re, Complex.smul_im, smul_eq_mul] <;> ring
  simpa only [P.coordinateEquiv.apply_symm_apply, Triangle.barycentric]
    using h (P.coordinateEquiv.symm z)

theorem Triangle.orientedDoubleArea_edge_vertex (P : Triangle) (k : Fin 3) :
    orientedDoubleArea (P.edgeStart k) (P.edgeEnd k) (P.vertex k) =
      orientedDoubleArea P.a P.b P.c := by
  rw [P.orientedDoubleArea_edge, P.barycentric_vertex, if_pos rfl, mul_one]

theorem Triangle.edgeVector_smul_of_same_line (P Q : Triangle) (k l : Fin 3)
    (hstart : P.barycentric (Q.edgeStart l) k = 0)
    (hend : P.barycentric (Q.edgeEnd l) k = 0) :
    ∃ t : ℝ, t ≠ 0 ∧ Q.edgeVector l = t • P.edgeVector k := by
  obtain ⟨u, hu⟩ := (P.barycentric_eq_zero_iff_lineMap k (Q.edgeStart l)).mp hstart
  obtain ⟨v, hv⟩ := (P.barycentric_eq_zero_iff_lineMap k (Q.edgeEnd l)).mp hend
  have hvec : Q.edgeVector l = (v - u) • P.edgeVector k := by
    unfold Triangle.edgeVector
    rw [← hu, ← hv]
    simp only [AffineMap.lineMap_apply_module', add_sub_add_right_eq_sub, sub_smul]
  refine ⟨v - u, ?_, hvec⟩
  intro h
  rw [h, zero_smul] at hvec
  exact Q.edgeVector_ne_zero l hvec

theorem orientedDoubleArea_of_edge_smul (A B C X Y : ℂ) (t : ℝ)
    (h : B - A = t • (Y - X)) :
    orientedDoubleArea A B C =
      t * (orientedDoubleArea X Y C - orientedDoubleArea X Y A) := by
  have hB : B = t • (Y - X) + A := (sub_eq_iff_eq_add).mp h
  rw [hB]
  simp only [orientedDoubleArea, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring

theorem Triangle.orientedDoubleArea_eq_of_edgeVector_smul
    (P Q : Triangle) (k l : Fin 3) (t : ℝ)
    (hvec : Q.edgeVector l = t • P.edgeVector k)
    (hstart : P.barycentric (Q.edgeStart l) k = 0) :
    orientedDoubleArea Q.a Q.b Q.c = t * orientedDoubleArea P.a P.b P.c *
      P.barycentric (Q.vertex l) k := by
  have h := orientedDoubleArea_of_edge_smul (Q.edgeStart l) (Q.edgeEnd l) (Q.vertex l)
    (P.edgeStart k) (P.edgeEnd k) t hvec
  rw [Q.orientedDoubleArea_edge_vertex, P.orientedDoubleArea_edge,
    P.orientedDoubleArea_edge, hstart, mul_zero, sub_zero] at h
  exact h.trans (by ring)

theorem Triangle.orientedEdgeVector_smul_of_same_line (P Q : Triangle) (k l : Fin 3)
    (hstart : P.barycentric (Q.edgeStart l) k = 0)
    (hend : P.barycentric (Q.edgeEnd l) k = 0) :
    ∃ d : ℝ, 0 < d * P.barycentric (Q.vertex l) k ∧
      Q.orientedEdgeVector l = d • P.orientedEdgeVector k := by
  obtain ⟨t, _, ht⟩ := P.edgeVector_smul_of_same_line Q k l hstart hend
  let d := Q.orientationSign * t * P.orientationSign
  have harea := P.orientedDoubleArea_eq_of_edgeVector_smul Q k l t ht hstart
  have heq : (d * P.barycentric (Q.vertex l) k) *
      (P.orientationSign * orientedDoubleArea P.a P.b P.c) =
      Q.orientationSign * orientedDoubleArea Q.a Q.b Q.c := by
    rw [harea]
    calc
      _ = (P.orientationSign * P.orientationSign) *
          (Q.orientationSign * t * orientedDoubleArea P.a P.b P.c *
            P.barycentric (Q.vertex l) k) := by dsimp [d]; ring
      _ = _ := by rw [P.orientationSign_mul_self]; ring
  refine ⟨d, ?_, ?_⟩
  · have hp : 0 < (d * P.barycentric (Q.vertex l) k) *
        (P.orientationSign * orientedDoubleArea P.a P.b P.c) :=
      heq.symm ▸ Q.orientationSign_area_pos
    exact pos_of_mul_pos_left hp P.orientationSign_area_pos.le
  · rw [Triangle.orientedEdgeVector, ht, smul_smul, Triangle.orientedEdgeVector, smul_smul]
    congr 1
    symm
    dsimp [d]
    calc
      _ = Q.orientationSign * t * (P.orientationSign * P.orientationSign) := by ring
      _ = _ := by rw [P.orientationSign_mul_self, mul_one]

theorem Triangle.unitEdgeVector_eq_of_positive_smul (P Q : Triangle) (k l : Fin 3)
    (d : ℝ) (hd : 0 < d)
    (hvec : Q.orientedEdgeVector l = d • P.orientedEdgeVector k) :
    Q.unitEdgeVector l = P.unitEdgeVector k := by
  have hnorm := congrArg norm hvec
  rw [Q.norm_orientedEdgeVector, norm_smul, P.norm_orientedEdgeVector,
    Real.norm_eq_abs, abs_of_pos hd] at hnorm
  have hcoef : (Q.sideLength l)⁻¹ * d = (P.sideLength k)⁻¹ := by
    rw [hnorm]
    field_simp [ne_of_gt hd, ne_of_gt (P.sideLength_pos k)]
  rw [Triangle.unitEdgeVector, hvec, smul_smul, hcoef]
  rfl

theorem Triangle.unitEdgeVector_eq_neg_of_negative_smul (P Q : Triangle) (k l : Fin 3)
    (d : ℝ) (hd : d < 0)
    (hvec : Q.orientedEdgeVector l = d • P.orientedEdgeVector k) :
    Q.unitEdgeVector l = -P.unitEdgeVector k := by
  have hnorm := congrArg norm hvec
  rw [Q.norm_orientedEdgeVector, norm_smul, P.norm_orientedEdgeVector,
    Real.norm_eq_abs, abs_of_neg hd] at hnorm
  have hcoef : (Q.sideLength l)⁻¹ * d = -(P.sideLength k)⁻¹ := by
    rw [hnorm]
    field_simp [ne_of_lt hd, ne_of_gt (P.sideLength_pos k)]
  rw [Triangle.unitEdgeVector, hvec, smul_smul, hcoef, neg_smul]
  rfl

theorem Triangle.unitEdgeVector_eq_of_edge_subset (P Q : Triangle) (k l : Fin 3)
    (hsub : Q.carrier ⊆ P.carrier) (hedge : Q.edge l ⊆ P.edge k) :
    Q.unitEdgeVector l = P.unitEdgeVector k := by
  have hs := ((P.mem_edge_iff k (Q.edgeStart l)).mp
    (hedge (left_mem_segment ℝ _ _))).2
  have he := ((P.mem_edge_iff k (Q.edgeEnd l)).mp
    (hedge (right_mem_segment ℝ _ _))).2
  obtain ⟨d, hd, hvec⟩ := P.orientedEdgeVector_smul_of_same_line Q k l hs he
  have hx := (P.mem_carrier_iff_barycentric (Q.vertex l)).mp
    (hsub (Q.vertex_mem_carrier l)) k
  exact P.unitEdgeVector_eq_of_positive_smul Q k l d (pos_of_mul_pos_left hd hx) hvec

theorem TriangleDissection.shared_open_edges_unitVector_neg
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N) {i j : Fin N}
    (hij : i ≠ j) (k l : Fin 3) {z : ℂ}
    (hi : z ∈ (T.tile i).openEdge k) (hj : z ∈ (T.tile j).openEdge l) :
    (T.tile j).unitEdgeVector l = -(T.tile i).unitEdgeVector k := by
  have hs := (T.shared_open_edges_same_supporting_line hij k l hi hj
    ((T.tile j).edgeStart l)).mpr ((T.tile j).barycentric_edgeStart_self l)
  have he := (T.shared_open_edges_same_supporting_line hij k l hi hj
    ((T.tile j).edgeEnd l)).mpr ((T.tile j).barycentric_edgeEnd_self l)
  have hx := (T.shared_open_edges_opposite_vertices hij k l hi hj).2
  obtain ⟨d, hd, hvec⟩ := (T.tile i).orientedEdgeVector_smul_of_same_line
    (T.tile j) k l hs he
  have hdneg : d < 0 := by
    rcases mul_pos_iff.mp hd with h | h
    · exact False.elim ((not_lt_of_ge hx.le) h.2)
    · exact h.1
  exact (T.tile i).unitEdgeVector_eq_neg_of_negative_smul (T.tile j) k l d hdneg hvec

theorem TriangleDissection.shared_open_edges_odd_cancel
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N)
    (φ : ℂ → ℝ) (hodd : ∀ w, φ (-w) = -φ w) {i j : Fin N}
    (hij : i ≠ j) (k l : Fin 3) {z : ℂ}
    (hi : z ∈ (T.tile i).openEdge k) (hj : z ∈ (T.tile j).openEdge l) :
    φ ((T.tile i).unitEdgeVector k) + φ ((T.tile j).unitEdgeVector l) = 0 := by
  rw [T.shared_open_edges_unitVector_neg hij k l hi hj, hodd, add_neg_cancel]

end Erdos633
