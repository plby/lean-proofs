import ErdosProblems.Erdos633b.BoundaryStarAngles
import ErdosProblems.Erdos633b.CornerAngles
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Every reference angle occurs exactly n times among the actual placed vertices. -/

namespace Erdos633b.Tiling

def Vertex {T : Triangle} {n : ℕ} (d : Tiling T n) :=
  Set.range (fun e : Fin n × Fin 3 => d.place e.1 (d.tile.points e.2))

instance {T : Triangle} {n : ℕ} (d : Tiling T n) : Finite d.Vertex := by
  unfold Vertex
  infer_instance

noncomputable instance {T : Triangle} {n : ℕ} (d : Tiling T n) : Fintype d.Vertex :=
  Fintype.ofFinite _

noncomputable def vertexAt {T : Triangle} {n : ℕ} (d : Tiling T n)
    (a : Fin n) (j : Fin 3) : d.Vertex :=
  ⟨d.place a (d.tile.points j), ⟨(a, j), rfl⟩⟩

noncomputable def vertexAngleCount {T : Triangle} {n : ℕ} (d : Tiling T n)
    (p : d.Vertex) (j : Fin 3) : ℕ :=
  Fintype.card {a : Fin n // d.vertexAt a j = p}

theorem sum_vertexAngleCount {T : Triangle} {n : ℕ} (d : Tiling T n) (j : Fin 3) :
    ∑ p : d.Vertex, d.vertexAngleCount p j = n := by
  classical
  simpa only [Fintype.card_sigma, vertexAngleCount, Fintype.card_fin] using
    Fintype.card_congr (Equiv.sigmaFiberEquiv (fun a : Fin n => d.vertexAt a j))

def vertexPieceEquiv {T : Triangle} {n : ℕ} (d : Tiling T n) (p : d.Vertex) :
    (Σ j : Fin 3, {a : Fin n // d.vertexAt a j = p}) ≃ d.VertexPiece p.val where
  toFun x := ⟨(x.2.val, x.1), congrArg Subtype.val x.2.property⟩
  invFun e := ⟨e.val.2, ⟨e.val.1, Subtype.ext e.property⟩⟩
  left_inv := by rintro ⟨j, a, ha⟩; rfl
  right_inv := by rintro ⟨⟨a, j⟩, h⟩; rfl

theorem vertex_angle_sum_eq_counts {T : Triangle} {n : ℕ} (d : Tiling T n)
    (p : d.Vertex) :
    (∑ e : d.VertexPiece p.val, d.tile.angle e.val.2) =
      ∑ j : Fin 3, (d.vertexAngleCount p j : ℝ) * d.tile.angle j := by
  classical
  have he := Fintype.sum_equiv (d.vertexPieceEquiv p)
    (fun x => d.tile.angle x.1) (fun e => d.tile.angle e.val.2) (fun _ => rfl)
  rw [← he, Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, vertexAngleCount]

noncomputable def outerVertex {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3) :
    d.Vertex := by
  refine ⟨T.points i, ?_⟩
  obtain ⟨a, j, h⟩ := d.outer_vertex_is_tile_vertex i
  exact ⟨(a, j), h⟩

@[simp] theorem outerVertex_val {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3) :
    (d.outerVertex i).val = T.points i := by
  rfl

theorem outerVertex_injective {T : Triangle} {n : ℕ} (d : Tiling T n) :
    Function.Injective d.outerVertex := by
  intro i j h
  apply T.independent.injective
  have hv := congrArg Subtype.val h
  simpa only [d.outerVertex_val] using hv

theorem vertexAngleCount_outer {T : Triangle} {n : ℕ} (d : Tiling T n) (i j : Fin 3) :
    d.vertexAngleCount (d.outerVertex i) j = d.cornerAngleCount i j := by
  classical
  let e : {a : Fin n // d.vertexAt a j = d.outerVertex i} ≃
      {e : d.CornerPiece i // e.val.2 = j} :=
    { toFun := fun a => ⟨⟨(a.val, j), by
        have hv := congrArg Subtype.val a.property
        simpa only [vertexAt, d.outerVertex_val] using hv⟩, rfl⟩
      invFun := fun e => ⟨e.val.val.1, by
        apply Subtype.ext
        change d.place e.val.val.1 (d.tile.points j) = (d.outerVertex i).val
        rw [d.outerVertex_val]
        simpa only [e.property] using e.val.property⟩
      left_inv := by intro a; rfl
      right_inv := by
        rintro ⟨⟨⟨a, k⟩, ha⟩, h⟩
        dsimp only at h
        subst k
        rfl }
  have hc := Fintype.card_congr e
  simpa only [vertexAngleCount, cornerAngleCount, Fintype.card_subtype] using hc

theorem vertexAngleCount_boundary_sum {T : Triangle} {n : ℕ} (d : Tiling T n)
    (p : d.Vertex) (i : Fin 3) (hp : p.val ∈ T.openEdge i) :
    (∑ j : Fin 3, (d.vertexAngleCount p j : ℝ) * d.tile.angle j) = Real.pi := by
  obtain ⟨⟨a, j⟩, ha⟩ := p.property
  rw [← d.vertex_angle_sum_eq_counts]
  exact d.boundary_vertex_angle_sum i hp a j ha

end Erdos633b.Tiling
