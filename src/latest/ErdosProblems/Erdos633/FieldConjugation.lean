import ErdosProblems.Erdos633.ConjugateOrientation

/-!
# Actual conjugate dissections over real field embeddings

For a congruent tiling represented by field-valued vertices, every real
embedding produces a geometric dissection. Polynomial side identities also
give congruence of the image tiles when their labels correspond to the
reference labels. Coverage, disjointness, and the orientation change are all
proved from the original tiling rather than assumed for the images.
-/

namespace Erdos633

noncomputable def CongruentTiling.conjugateFieldDissection
    {F : Type*} [Field F] (P : FieldTriangle F) (τ σ : F →+* ℝ)
    {R : Triangle} {N : ℕ} (T : CongruentTiling (P.realize τ) R N)
    (Q : Fin N → FieldTriangle F) (hQ : ∀ i : Fin N, T.tile i = (Q i).realize τ) :
    TriangleDissection (P.realize σ) N :=
  T.toTriangleDissection.mapVertexImages (embeddingPointMap τ σ)
    (T.toTriangleDissection.edgeLinePreserving_embeddingPointMap τ σ
      (T.toTriangleDissection.vertices_in_fieldPoint_range τ Q hQ))
    (P.realize σ) (fun i => (Q i).realize σ) (P.realize_vertexImage τ σ)
    (fun i => by rw [hQ i]; exact (Q i).realize_vertexImage τ σ)
    (fun i => by
      rw [hQ i]
      apply (P.orientation_ratio_transfer (Q i) τ σ N T.card_pos ?_).symm
      simpa only [hQ i] using T.abs_doubleArea_eq_tile i)

/-- The hypotheses on squared sides concern only the original realization.
The new congruence witnesses are constructed after applying the embedding. -/
noncomputable def CongruentTiling.conjugateFieldTriangles
    {F : Type*} [Field F] (P R : FieldTriangle F) (τ σ : F →+* ℝ) {N : ℕ}
    (T : CongruentTiling (P.realize τ) (R.realize τ) N)
    (Q : Fin N → FieldTriangle F) (hQ : ∀ i : Fin N, T.tile i = (Q i).realize τ)
    (hab : ∀ i : Fin N, Complex.normSq ((R.realize τ).b - (R.realize τ).a) =
      Complex.normSq (((Q i).realize τ).b - ((Q i).realize τ).a))
    (hac : ∀ i : Fin N, Complex.normSq ((R.realize τ).c - (R.realize τ).a) =
      Complex.normSq (((Q i).realize τ).c - ((Q i).realize τ).a))
    (hbc : ∀ i : Fin N, Complex.normSq ((R.realize τ).c - (R.realize τ).b) =
      Complex.normSq (((Q i).realize τ).c - ((Q i).realize τ).b)) :
    CongruentTiling (P.realize σ) (R.realize σ) N where
  toTriangleDissection := T.conjugateFieldDissection P τ σ Q hQ
  congruent := fun i => R.congruent_realize_of_normSq (Q i) τ σ (hab i) (hac i) (hbc i)

theorem CongruentTiling.conjugateFieldDissection_vertexImage
    {F : Type*} [Field F] (P : FieldTriangle F) (τ σ : F →+* ℝ)
    {R : Triangle} {N : ℕ} (T : CongruentTiling (P.realize τ) R N)
    (Q : Fin N → FieldTriangle F) (hQ : ∀ i : Fin N, T.tile i = (Q i).realize τ)
    (i : Fin N) : (T.tile i).VertexImage
      ((T.conjugateFieldDissection P τ σ Q hQ).tile i) (embeddingPointMap τ σ) := by
  change (T.tile i).VertexImage ((Q i).realize σ) (embeddingPointMap τ σ)
  rw [hQ i]
  exact (Q i).realize_vertexImage τ σ

theorem CongruentTiling.conjugateFieldDissection_vertex_injective
    {F : Type*} [Field F] (P : FieldTriangle F) (τ σ : F →+* ℝ)
    {R : Triangle} {N : ℕ} (T : CongruentTiling (P.realize τ) R N)
    (Q : Fin N → FieldTriangle F) (hQ : ∀ i : Fin N, T.tile i = (Q i).realize τ) :
    Set.InjOn (embeddingPointMap τ σ) T.toTriangleDissection.vertexFinset :=
  (embeddingPointMap_injOn τ σ).mono
    (T.toTriangleDissection.vertices_in_fieldPoint_range τ Q hQ)

end Erdos633
