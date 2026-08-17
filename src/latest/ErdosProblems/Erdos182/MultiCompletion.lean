import ErdosProblems.Erdos182.MultiColor

/-!
# Completing a bounded-degree bipartite multigraph to a regular one

The construction pads the two vertex classes to `L ⊕ R` and `R ⊕ L`.
The missing incidences on the two padded sides have the same cardinality, so
they may be paired to form new labelled edges.  Original edges embed and keep
both endpoints.
-/

open scoped Classical

namespace Erdos182
namespace BipartiteMultigraph

universe uL uR uE

variable {L : Type uL} {R : Type uR} {E : Type uE}
  [Fintype L] [Fintype R] [Fintype E]

private noncomputable def leftDegree (G : BipartiteMultigraph L R E) (l : L) : ℕ :=
  Nat.card {e : E // G.left e = l}

private noncomputable def rightDegree (G : BipartiteMultigraph L R E) (r : R) : ℕ :=
  Nat.card {e : E // G.right e = r}

private noncomputable def paddedLeftDegree (G : BipartiteMultigraph L R E) :
    L ⊕ R → ℕ
  | .inl l => leftDegree G l
  | .inr _ => 0

private noncomputable def paddedRightDegree (G : BipartiteMultigraph L R E) :
    R ⊕ L → ℕ
  | .inl r => rightDegree G r
  | .inr _ => 0

private abbrev LeftStub (G : BipartiteMultigraph L R E) (D : ℕ) :=
  Σ x : L ⊕ R, Fin (D - paddedLeftDegree G x)

private abbrev RightStub (G : BipartiteMultigraph L R E) (D : ℕ) :=
  Σ x : R ⊕ L, Fin (D - paddedRightDegree G x)

private lemma sum_leftDegree (G : BipartiteMultigraph L R E) :
    ∑ l, leftDegree G l = Nat.card E := by
  classical
  simp only [leftDegree]
  rw [← Nat.card_sigma]
  exact Nat.card_congr (Equiv.sigmaFiberEquiv G.left)

private lemma sum_rightDegree (G : BipartiteMultigraph L R E) :
    ∑ r, rightDegree G r = Nat.card E := by
  classical
  simp only [rightDegree]
  rw [← Nat.card_sigma]
  exact Nat.card_congr (Equiv.sigmaFiberEquiv G.right)

private lemma card_leftStub (G : BipartiteMultigraph L R E) (D : ℕ)
    (hleft : ∀ l, leftDegree G l ≤ D) :
    Nat.card (LeftStub G D) =
      (Nat.card L + Nat.card R) * D - Nat.card E := by
  classical
  rw [Nat.card_sigma]
  simp only [Nat.card_fin]
  rw [Fintype.sum_sum_type]
  simp only [paddedLeftDegree]
  rw [Finset.sum_tsub_distrib Finset.univ (by
    intro l _
    exact hleft l)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [sum_leftDegree]
  have hedges : Nat.card E ≤ Nat.card L * D := by
    rw [← sum_leftDegree G]
    calc
      ∑ l, leftDegree G l ≤ ∑ _l : L, D := by
        apply Finset.sum_le_sum
        intro l _
        exact hleft l
      _ = Nat.card L * D := by simp [Nat.card_eq_fintype_card]
  simp only [← Nat.card_eq_fintype_card, Nat.sub_zero, Nat.add_mul]
  exact (Nat.sub_add_comm hedges).symm

private lemma card_rightStub (G : BipartiteMultigraph L R E) (D : ℕ)
    (hright : ∀ r, rightDegree G r ≤ D) :
    Nat.card (RightStub G D) =
      (Nat.card L + Nat.card R) * D - Nat.card E := by
  classical
  rw [Nat.card_sigma]
  simp only [Nat.card_fin]
  rw [Fintype.sum_sum_type]
  simp only [paddedRightDegree]
  rw [Finset.sum_tsub_distrib Finset.univ (by
    intro r _
    exact hright r)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [sum_rightDegree]
  have hedges : Nat.card E ≤ Nat.card R * D := by
    rw [← sum_rightDegree G]
    calc
      ∑ r, rightDegree G r ≤ ∑ _r : R, D := by
        apply Finset.sum_le_sum
        intro r _
        exact hright r
      _ = Nat.card R * D := by simp [Nat.card_eq_fintype_card]
  simp only [← Nat.card_eq_fintype_card, Nat.sub_zero, Nat.add_mul]
  calc
    Nat.card R * D - Nat.card E + Nat.card L * D =
        Nat.card R * D + Nat.card L * D - Nat.card E :=
      (Nat.sub_add_comm hedges).symm
    _ = Nat.card L * D + Nat.card R * D - Nat.card E := by
      rw [Nat.add_comm]

/-- Data witnessing an embedding of a bounded-degree bipartite multigraph in a
regular bipartite multigraph.  The new sides are the balanced padded types
`L ⊕ R` and `R ⊕ L`; the edge type is exposed abstractly through this
structure because consumers only need its finite instance and its embedding. -/
structure RegularCompletion (G : BipartiteMultigraph L R E) (D : ℕ) where
  Edge : Type (max uL uR uE)
  instFintypeEdge : Fintype Edge
  graph : BipartiteMultigraph (L ⊕ R) (R ⊕ L) Edge
  regular : graph.IsRegular D
  edgeEmbedding : E ↪ Edge
  leftEmbedding : L ↪ L ⊕ R := Function.Embedding.inl
  rightEmbedding : R ↪ R ⊕ L := Function.Embedding.inl
  map_left : ∀ e, graph.left (edgeEmbedding e) = leftEmbedding (G.left e)
  map_right : ∀ e, graph.right (edgeEmbedding e) = rightEmbedding (G.right e)

attribute [instance] RegularCompletion.instFintypeEdge

private noncomputable def stubEquiv (G : BipartiteMultigraph L R E) (D : ℕ)
    (hleft : ∀ l, leftDegree G l ≤ D)
    (hright : ∀ r, rightDegree G r ≤ D) :
    LeftStub G D ≃ RightStub G D :=
  Fintype.equivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card] using
      (card_leftStub G D hleft).trans (card_rightStub G D hright).symm)

private noncomputable def completionGraph (G : BipartiteMultigraph L R E) (D : ℕ)
    (hleft : ∀ l, leftDegree G l ≤ D)
    (hright : ∀ r, rightDegree G r ≤ D) :
    BipartiteMultigraph (L ⊕ R) (R ⊕ L) (E ⊕ LeftStub G D) where
  left
    | .inl e => .inl (G.left e)
    | .inr s => s.1
  right
    | .inl e => .inl (G.right e)
    | .inr s => (stubEquiv G D hleft hright s).1

private def sigmaFstFiberEquiv {X : Type*} (F : X → Type*) (x : X) :
    {s : Σ y, F y // s.1 = x} ≃ F x where
  toFun
    | ⟨⟨y, z⟩, h⟩ => h ▸ z
  invFun z := ⟨⟨x, z⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨y, z⟩, h⟩
    cases h
    rfl
  right_inv _ := rfl

private def equivFiberEquiv {X Y Z : Type*} (e : X ≃ Y) (f : Y → Z) (z : Z) :
    {x : X // f (e x) = z} ≃ {y : Y // f y = z} where
  toFun x := ⟨e x, x.2⟩
  invFun y := ⟨e.symm y, by simpa using y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp

private def completionLeftEdgeFiberEquiv
    (G : BipartiteMultigraph L R E) (D : ℕ)
    (hleft : ∀ l, leftDegree G l ≤ D)
    (hright : ∀ r, rightDegree G r ≤ D) (x : L ⊕ R) :
    {e : E // (completionGraph G D hleft hright).left (Sum.inl e) = x} ≃
      {e : E // Sum.inl (G.left e) = x} where
  toFun e := ⟨e, by simpa only [completionGraph] using e.2⟩
  invFun e := ⟨e, by simpa only [completionGraph] using e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def completionLeftStubFiberEquiv
    (G : BipartiteMultigraph L R E) (D : ℕ)
    (hleft : ∀ l, leftDegree G l ≤ D)
    (hright : ∀ r, rightDegree G r ≤ D) (x : L ⊕ R) :
    {s : LeftStub G D // (completionGraph G D hleft hright).left (Sum.inr s) = x} ≃
      {s : LeftStub G D // s.1 = x} where
  toFun s := ⟨s, by simpa only [completionGraph] using s.2⟩
  invFun s := ⟨s, by simpa only [completionGraph] using s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def completionRightEdgeFiberEquiv
    (G : BipartiteMultigraph L R E) (D : ℕ)
    (hleft : ∀ l, leftDegree G l ≤ D)
    (hright : ∀ r, rightDegree G r ≤ D) (x : R ⊕ L) :
    {e : E // (completionGraph G D hleft hright).right (Sum.inl e) = x} ≃
      {e : E // Sum.inl (G.right e) = x} where
  toFun e := ⟨e, by simpa only [completionGraph] using e.2⟩
  invFun e := ⟨e, by simpa only [completionGraph] using e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def completionRightStubFiberEquiv
    (G : BipartiteMultigraph L R E) (D : ℕ)
    (hleft : ∀ l, leftDegree G l ≤ D)
    (hright : ∀ r, rightDegree G r ≤ D) (x : R ⊕ L) :
    {s : LeftStub G D // (completionGraph G D hleft hright).right (Sum.inr s) = x} ≃
      {s : LeftStub G D // (stubEquiv G D hleft hright s).1 = x} where
  toFun s := ⟨s, by simpa only [completionGraph] using s.2⟩
  invFun s := ⟨s, by simpa only [completionGraph] using s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma card_sum_fiber_left (G : BipartiteMultigraph L R E) (D : ℕ)
    (hleft : ∀ l, leftDegree G l ≤ D)
    (hright : ∀ r, rightDegree G r ≤ D) (x : L ⊕ R) :
    Nat.card {e : E ⊕ LeftStub G D //
      (completionGraph G D hleft hright).left e = x} = D := by
  classical
  rw [Nat.card_congr Equiv.subtypeSum, Nat.card_sum]
  rw [Nat.card_congr (completionLeftEdgeFiberEquiv G D hleft hright x),
    Nat.card_congr (completionLeftStubFiberEquiv G D hleft hright x)]
  cases x with
  | inl l =>
      change Nat.card {e : E // Sum.inl (G.left e) = Sum.inl l} +
        Nat.card {s : LeftStub G D // s.1 = Sum.inl l} = D
      rw [show Nat.card {e : E // Sum.inl (G.left e) = Sum.inl l} =
          leftDegree G l by simp [leftDegree],
        Nat.card_congr
          (sigmaFstFiberEquiv
            (fun x ↦ Fin (D - paddedLeftDegree G x)) (Sum.inl l))]
      simp only [Nat.card_fin, paddedLeftDegree]
      exact Nat.add_sub_of_le (hleft l)
  | inr r =>
      change Nat.card {e : E // Sum.inl (G.left e) = Sum.inr r} +
        Nat.card {s : LeftStub G D // s.1 = Sum.inr r} = D
      rw [Nat.card_congr
          (sigmaFstFiberEquiv
            (fun x ↦ Fin (D - paddedLeftDegree G x)) (Sum.inr r))]
      rw [Nat.card_fin]
      simp [paddedLeftDegree]

private lemma card_sum_fiber_right (G : BipartiteMultigraph L R E) (D : ℕ)
    (hleft : ∀ l, leftDegree G l ≤ D)
    (hright : ∀ r, rightDegree G r ≤ D) (x : R ⊕ L) :
    Nat.card {e : E ⊕ LeftStub G D //
      (completionGraph G D hleft hright).right e = x} = D := by
  classical
  rw [Nat.card_congr Equiv.subtypeSum, Nat.card_sum]
  rw [Nat.card_congr (completionRightEdgeFiberEquiv G D hleft hright x),
    Nat.card_congr (completionRightStubFiberEquiv G D hleft hright x)]
  cases x with
  | inl r =>
      change Nat.card {e : E // Sum.inl (G.right e) = Sum.inl r} +
        Nat.card {s : LeftStub G D //
          (stubEquiv G D hleft hright s).1 = Sum.inl r} = D
      rw [show Nat.card {e : E // Sum.inl (G.right e) = Sum.inl r} =
          rightDegree G r by simp [rightDegree],
        Nat.card_congr
          (equivFiberEquiv (stubEquiv G D hleft hright) Sigma.fst (Sum.inl r)),
        Nat.card_congr
          (sigmaFstFiberEquiv
            (fun x ↦ Fin (D - paddedRightDegree G x)) (Sum.inl r))]
      simp only [Nat.card_fin, paddedRightDegree]
      exact Nat.add_sub_of_le (hright r)
  | inr l =>
      change Nat.card {e : E // Sum.inl (G.right e) = Sum.inr l} +
        Nat.card {s : LeftStub G D //
          (stubEquiv G D hleft hright s).1 = Sum.inr l} = D
      rw [Nat.card_congr
          (equivFiberEquiv (stubEquiv G D hleft hright) Sigma.fst (Sum.inr l)),
        Nat.card_congr
          (sigmaFstFiberEquiv
            (fun x ↦ Fin (D - paddedRightDegree G x)) (Sum.inr l))]
      rw [Nat.card_fin]
      simp [paddedRightDegree]

/-- Every finite bipartite multigraph of maximum degree at most `D` embeds in
a finite `D`-regular bipartite multigraph. -/
theorem exists_regularCompletion (G : BipartiteMultigraph L R E) (D : ℕ)
    (hleft : ∀ l, Fintype.card {e : E // G.left e = l} ≤ D)
    (hright : ∀ r, Fintype.card {e : E // G.right e = r} ≤ D) :
    Nonempty (RegularCompletion G D) := by
  have hleft' : ∀ l, leftDegree G l ≤ D := by
    intro l
    simpa only [leftDegree, Nat.card_eq_fintype_card] using hleft l
  have hright' : ∀ r, rightDegree G r ≤ D := by
    intro r
    simpa only [rightDegree, Nat.card_eq_fintype_card] using hright r
  let ι : E ↪ E ⊕ LeftStub G D := Function.Embedding.inl
  refine ⟨{
    Edge := E ⊕ LeftStub G D
    instFintypeEdge := inferInstance
    graph := completionGraph G D hleft' hright'
    regular := ⟨?_, ?_⟩
    edgeEmbedding := ι
    map_left := ?_
    map_right := ?_ }⟩
  · intro l
    let Fiber := {e : E ⊕ LeftStub G D //
      (completionGraph G D hleft' hright').left e = l}
    let instFiber : Fintype Fiber := @Subtype.fintype _ _
      (fun e ↦ Classical.propDecidable
        ((completionGraph G D hleft' hright').left e = l)) inferInstance
    change @Fintype.card Fiber instFiber = D
    rw [← @Nat.card_eq_fintype_card Fiber instFiber]
    exact card_sum_fiber_left G D hleft' hright' l
  · intro r
    let Fiber := {e : E ⊕ LeftStub G D //
      (completionGraph G D hleft' hright').right e = r}
    let instFiber : Fintype Fiber := @Subtype.fintype _ _
      (fun e ↦ Classical.propDecidable
        ((completionGraph G D hleft' hright').right e = r)) inferInstance
    change @Fintype.card Fiber instFiber = D
    rw [← @Nat.card_eq_fintype_card Fiber instFiber]
    exact card_sum_fiber_right G D hleft' hright' r
  · intro e
    rfl
  · intro e
    rfl

/-- The bounded-degree form of Kőnig's line-colouring theorem. -/
theorem exists_properColoring_of_degree_le
    (G : BipartiteMultigraph L R E) (D : ℕ)
    (hleft : ∀ l, Fintype.card {e : E // G.left e = l} ≤ D)
    (hright : ∀ r, Fintype.card {e : E // G.right e = r} ≤ D) :
    Nonempty (G.ProperColoring D) := by
  obtain ⟨K⟩ := exists_regularCompletion G D hleft hright
  obtain ⟨C⟩ := exists_properColoring K.graph K.regular
  refine ⟨{
    color := fun e ↦ C.color (K.edgeEmbedding e)
    left_injective := ?_
    right_injective := ?_ }⟩
  · intro l e₁ e₂ hc
    have h₁ : K.graph.left (K.edgeEmbedding e₁.1) = K.leftEmbedding l := by
      rw [K.map_left, e₁.2]
    have h₂ : K.graph.left (K.edgeEmbedding e₂.1) = K.leftEmbedding l := by
      rw [K.map_left, e₂.2]
    have he := C.left_injective (K.leftEmbedding l)
      (a₁ := ⟨K.edgeEmbedding e₁.1, h₁⟩)
      (a₂ := ⟨K.edgeEmbedding e₂.1, h₂⟩) hc
    apply Subtype.ext
    exact K.edgeEmbedding.injective (congrArg Subtype.val he)
  · intro r e₁ e₂ hc
    have h₁ : K.graph.right (K.edgeEmbedding e₁.1) = K.rightEmbedding r := by
      rw [K.map_right, e₁.2]
    have h₂ : K.graph.right (K.edgeEmbedding e₂.1) = K.rightEmbedding r := by
      rw [K.map_right, e₂.2]
    have he := C.right_injective (K.rightEmbedding r)
      (a₁ := ⟨K.edgeEmbedding e₁.1, h₁⟩)
      (a₂ := ⟨K.edgeEmbedding e₂.1, h₂⟩) hc
    apply Subtype.ext
    exact K.edgeEmbedding.injective (congrArg Subtype.val he)

end BipartiteMultigraph
end Erdos182
