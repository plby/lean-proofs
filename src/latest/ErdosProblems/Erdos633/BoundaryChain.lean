import ErdosProblems.Erdos633.LineBoundary

/-!
# The full directed boundary identity of an actual dissection

Cancellation on each supporting line is summed over the finite set of edge
lines. The resulting identity applies to every edge function additive on the
collinear triples of marked vertices that occur in the original dissection.
The function need not be continuous or preserve the order of marked points.
-/

namespace Erdos633

open scoped BigOperators

def Triangle.edgeLine (P : Triangle) (k : Fin 3) : Set ℂ :=
  Set.range (AffineMap.lineMap (P.edgeStart k) (P.edgeEnd k) : ℝ → ℂ)

theorem Triangle.edgeStart_mem_edgeLine (P : Triangle) (k : Fin 3) :
    P.edgeStart k ∈ P.edgeLine k := ⟨0, AffineMap.lineMap_apply_zero _ _⟩

theorem Triangle.edgeEnd_mem_edgeLine (P : Triangle) (k : Fin 3) :
    P.edgeEnd k ∈ P.edgeLine k := ⟨1, AffineMap.lineMap_apply_one _ _⟩

theorem Triangle.edgeLine_eq_axis_iff (P : Triangle) (k : Fin 3) (p d : ℂ) (hd : d ≠ 0) :
    P.edgeLine k = Set.range (axisMap p d) ↔
      OnAxis p d (P.edgeStart k) ∧ OnAxis p d (P.edgeEnd k) := by
  constructor
  · intro h
    constructor
    · apply (onAxis_iff_mem_range p d _ hd).mpr
      rw [← h]
      exact P.edgeStart_mem_edgeLine k
    · apply (onAxis_iff_mem_range p d _ hd).mpr
      rw [← h]
      exact P.edgeEnd_mem_edgeLine k
  · rintro ⟨hs, he⟩
    let a := axisParameter p d (P.edgeStart k)
    let b := axisParameter p d (P.edgeEnd k)
    have ha : P.edgeStart k = axisMap p d a :=
      (axisMap_axisParameter p d _ hd hs).symm
    have hb : P.edgeEnd k = axisMap p d b :=
      (axisMap_axisParameter p d _ hd he).symm
    have hab : b - a ≠ 0 := by
      intro h
      exact P.edgeStart_ne_edgeEnd k (by rw [ha, hb, sub_eq_zero.mp h])
    have hsur : Function.Surjective (AffineMap.lineMap a b : ℝ → ℝ) := by
      intro t
      refine ⟨(t - a) / (b - a), ?_⟩
      rw [AffineMap.lineMap_apply_ring', div_mul_cancel₀ _ hab]
      ring
    apply Set.Subset.antisymm
    · rintro z ⟨t, rfl⟩
      refine ⟨AffineMap.lineMap a b t, ?_⟩
      rw [(axisMap p d).apply_lineMap, ← ha, ← hb]
    · rintro z ⟨t, rfl⟩
      obtain ⟨u, hu⟩ := hsur t
      refine ⟨u, ?_⟩
      rw [ha, hb, ← (axisMap p d).apply_lineMap, hu]

theorem Triangle.edgeLine_eq_own_axis (P : Triangle) (k : Fin 3) :
    P.edgeLine k = Set.range (axisMap (P.edgeStart k) (P.edgeVector k)) := by
  have h : P.edgeStart k + (P.edgeEnd k - P.edgeStart k) = P.edgeEnd k := by abel
  simp only [Triangle.edgeLine, axisMap, Triangle.edgeVector, h]

noncomputable def Triangle.directedBoundaryValue (P : Triangle) (f : ℂ → ℂ → ℝ) : ℝ :=
  ∑ k : Fin 3, P.orientationSign * f (P.edgeStart k) (P.edgeEnd k)

noncomputable def Triangle.lineBoundaryValue (P : Triangle) (L : Set ℂ)
    (f : ℂ → ℂ → ℝ) : ℝ := by
  classical
  exact ∑ k : Fin 3, if P.edgeLine k = L then
    P.orientationSign * f (P.edgeStart k) (P.edgeEnd k) else 0

theorem Triangle.axisEndpointSum_eq_lineBoundaryValue (P : Triangle) (p d : ℂ)
    (hd : d ≠ 0) (f : ℂ → ℂ → ℝ)
    (hadd : ∀ k : Fin 3, OnAxis p d (P.edgeStart k) → OnAxis p d (P.edgeEnd k) →
      f p (P.edgeStart k) + f (P.edgeStart k) (P.edgeEnd k) = f p (P.edgeEnd k)) :
    P.axisEndpointSum p d (fun t => f p (axisMap p d t)) =
      P.lineBoundaryValue (Set.range (axisMap p d)) f := by
  classical
  unfold Triangle.axisEndpointSum Triangle.lineBoundaryValue
  apply Finset.sum_congr rfl
  intro k _
  by_cases hline : OnAxis p d (P.edgeStart k) ∧ OnAxis p d (P.edgeEnd k)
  · rw [Triangle.axisEdgeWeight, if_pos hline,
      if_pos ((P.edgeLine_eq_axis_iff k p d hd).mpr hline)]
    dsimp only
    rw [axisMap_axisParameter p d _ hd hline.1, axisMap_axisParameter p d _ hd hline.2]
    congr 1
    linarith [hadd k hline.1 hline.2]
  · rw [Triangle.axisEdgeWeight, if_neg hline, zero_mul,
      if_neg (fun h => hline ((P.edgeLine_eq_axis_iff k p d hd).mp h))]

theorem Triangle.sum_lineBoundaryValue (P : Triangle) (S : Finset (Set ℂ))
    (hS : ∀ k : Fin 3, P.edgeLine k ∈ S) (f : ℂ → ℂ → ℝ) :
    (∑ L ∈ S, P.lineBoundaryValue L f) = P.directedBoundaryValue f := by
  classical
  unfold Triangle.lineBoundaryValue Triangle.directedBoundaryValue
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp [hS k]

def TriangleDissection.EdgeAdditive {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (f : ℂ → ℂ → ℝ) : Prop :=
  ∀ Q : Triangle, (Q = P ∨ ∃ i : Fin N, Q = T.tile i) → ∀ k : Fin 3,
    ∀ a ∈ T.vertexFinset, ∀ b ∈ T.vertexFinset,
      OnAxis (Q.edgeStart k) (Q.edgeVector k) a →
      OnAxis (Q.edgeStart k) (Q.edgeVector k) b →
      f (Q.edgeStart k) a + f a b = f (Q.edgeStart k) b

theorem TriangleDissection.edgeStart_mem_vertexFinset
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N)
    (Q : Triangle) (hQ : Q = P ∨ ∃ i : Fin N, Q = T.tile i) (k : Fin 3) :
    Q.edgeStart k ∈ T.vertexFinset := by
  obtain ⟨j, hj⟩ := Q.edgeStart_mem_vertices k
  rw [← hj]
  rcases hQ with rfl | ⟨i, rfl⟩
  · exact T.outer_vertex_mem_vertexFinset j
  · exact (T.mem_vertexFinset _).mpr ⟨i, j, rfl⟩

theorem TriangleDissection.edgeEnd_mem_vertexFinset
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N)
    (Q : Triangle) (hQ : Q = P ∨ ∃ i : Fin N, Q = T.tile i) (k : Fin 3) :
    Q.edgeEnd k ∈ T.vertexFinset := by
  obtain ⟨j, hj⟩ := Q.edgeEnd_mem_vertices k
  rw [← hj]
  rcases hQ with rfl | ⟨i, rfl⟩
  · exact T.outer_vertex_mem_vertexFinset j
  · exact (T.mem_vertexFinset _).mpr ⟨i, j, rfl⟩

theorem TriangleDissection.lineBoundaryValue_eq_sum
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N)
    (f : ℂ → ℂ → ℝ) (hf : T.EdgeAdditive f)
    (Q : Triangle) (hQ : Q = P ∨ ∃ i : Fin N, Q = T.tile i) (k : Fin 3) :
    P.lineBoundaryValue (Q.edgeLine k) f =
      ∑ i : Fin N, (T.tile i).lineBoundaryValue (Q.edgeLine k) f := by
  let p := Q.edgeStart k
  let d := Q.edgeVector k
  have hd : d ≠ 0 := Q.edgeVector_ne_zero k
  have heq (R : Triangle) (hR : R = P ∨ ∃ i : Fin N, R = T.tile i) :
      R.axisEndpointSum p d (fun t => f p (axisMap p d t)) =
        R.lineBoundaryValue (Q.edgeLine k) f := by
    rw [Q.edgeLine_eq_own_axis]
    apply R.axisEndpointSum_eq_lineBoundaryValue p d hd f
    intro l hs he
    exact hf Q hQ k _ (T.edgeStart_mem_vertexFinset R hR l)
      _ (T.edgeEnd_mem_vertexFinset R hR l) hs he
  have h := T.axisEndpointSum_eq_sum p d hd (fun t => f p (axisMap p d t))
  simpa only [heq P (Or.inl rfl), heq (T.tile _) (Or.inr ⟨_, rfl⟩)] using h

/-- Full directed-edge cancellation is derived from the original coverage and
disjoint interiors. It is not an additional hypothesis on a tiling. -/
theorem TriangleDissection.directedBoundaryValue_eq_sum
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N)
    (f : ℂ → ℂ → ℝ) (hf : T.EdgeAdditive f) :
    P.directedBoundaryValue f = ∑ i : Fin N, (T.tile i).directedBoundaryValue f := by
  classical
  let S := Finset.univ.image P.edgeLine ∪
    (Finset.univ : Finset (Fin N × Fin 3)).image (fun j => (T.tile j.1).edgeLine j.2)
  have hP (k : Fin 3) : P.edgeLine k ∈ S :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)
  have hQ (i : Fin N) (k : Fin 3) : (T.tile i).edgeLine k ∈ S :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i, k), Finset.mem_univ _, rfl⟩)
  have hline (L : Set ℂ) (hL : L ∈ S) :
      P.lineBoundaryValue L f = ∑ i : Fin N, (T.tile i).lineBoundaryValue L f := by
    rcases Finset.mem_union.mp hL with hL | hL
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hL
      exact T.lineBoundaryValue_eq_sum f hf P (Or.inl rfl) k
    · obtain ⟨⟨i, k⟩, _, rfl⟩ := Finset.mem_image.mp hL
      exact T.lineBoundaryValue_eq_sum f hf (T.tile i) (Or.inr ⟨i, rfl⟩) k
  calc
    P.directedBoundaryValue f = ∑ L ∈ S, P.lineBoundaryValue L f :=
      (P.sum_lineBoundaryValue S hP f).symm
    _ = ∑ L ∈ S, ∑ i : Fin N, (T.tile i).lineBoundaryValue L f :=
      Finset.sum_congr rfl hline
    _ = ∑ i : Fin N, (T.tile i).directedBoundaryValue f := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun i _ => (T.tile i).sum_lineBoundaryValue S (hQ i) f)

end Erdos633
