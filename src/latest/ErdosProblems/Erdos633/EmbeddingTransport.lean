import ErdosProblems.Erdos633.FieldRigidity

/-!
# Marked edge lines under real field embeddings

The map between two real realizations of field-valued points is defined on
the entire plane, with arbitrary value zero outside the source realization.
Its behavior on the tiling vertices is exact and injective. Polynomial
determinants prove the supporting-line hypotheses of geometric transport.
-/

namespace Erdos633

noncomputable def embeddingPointMap {F : Type*} [Field F]
    (τ σ : F →+* ℝ) (z : ℂ) : ℂ := by
  classical
  exact if h : ∃ p : F × F, fieldPoint τ p = z then fieldPoint σ h.choose else 0

theorem embeddingPointMap_fieldPoint {F : Type*} [Field F]
    (τ σ : F →+* ℝ) (p : F × F) :
    embeddingPointMap τ σ (fieldPoint τ p) = fieldPoint σ p := by
  classical
  have h : ∃ q : F × F, fieldPoint τ q = fieldPoint τ p := ⟨p, rfl⟩
  rw [embeddingPointMap, dif_pos h]
  exact congrArg (fieldPoint σ) ((fieldPoint_injective τ) h.choose_spec)

theorem embeddingPointMap_injOn {F : Type*} [Field F] (τ σ : F →+* ℝ) :
    Set.InjOn (embeddingPointMap τ σ) (Set.range (fieldPoint τ)) := by
  rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ h
  simp only [embeddingPointMap_fieldPoint] at h
  exact congrArg (fieldPoint τ) ((fieldPoint_injective σ) h)

theorem onAxis_iff_doubleArea_zero (p q z : ℂ) (hpq : p ≠ q) :
    OnAxis p (q - p) z ↔ orientedDoubleArea p q z = 0 := by
  have hn : Complex.normSq (q - p) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr (sub_ne_zero.mpr hpq.symm))
  have h : ((z - p) / (q - p)).im =
      orientedDoubleArea p q z / Complex.normSq (q - p) := by
    rw [Complex.div_im, orientedDoubleArea]
    ring
  simp only [OnAxis, h, div_eq_zero_iff, hn, or_false]

theorem fieldPoint_onAxis_transfer {F : Type*} [Field F] (τ σ : F →+* ℝ)
    (p q z : F × F) (hpq : fieldPoint τ p ≠ fieldPoint τ q)
    (h : OnAxis (fieldPoint τ p) (fieldPoint τ q - fieldPoint τ p) (fieldPoint τ z)) :
    OnAxis (fieldPoint σ p) (fieldPoint σ q - fieldPoint σ p) (fieldPoint σ z) := by
  have hne : fieldPoint σ p ≠ fieldPoint σ q := by
    intro heq
    exact hpq (congrArg (fieldPoint τ) ((fieldPoint_injective σ) heq))
  apply (onAxis_iff_doubleArea_zero _ _ _ hne).mpr
  have hz := (onAxis_iff_doubleArea_zero _ _ _ hpq).mp h
  rw [orientedDoubleArea_fieldPoint] at hz ⊢
  have hzero : fieldDoubleArea p q z = 0 := τ.injective (hz.trans τ.map_zero.symm)
  rw [hzero, map_zero]

theorem TriangleDissection.edgeLinePreserving_embeddingPointMap
    {F : Type*} [Field F] (τ σ : F →+* ℝ)
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N)
    (hV : ∀ z ∈ T.vertexFinset, z ∈ Set.range (fieldPoint τ)) :
    T.EdgeLinePreserving (embeddingPointMap τ σ) := by
  intro Q hQ k
  obtain ⟨p, hp⟩ := hV _ (T.edgeStart_mem_vertexFinset Q hQ k)
  obtain ⟨q, hq⟩ := hV _ (T.edgeEnd_mem_vertexFinset Q hQ k)
  have hpq : fieldPoint τ p ≠ fieldPoint τ q := by
    rw [hp, hq]
    exact Q.edgeStart_ne_edgeEnd k
  constructor
  · rw [← hp, ← hq, embeddingPointMap_fieldPoint, embeddingPointMap_fieldPoint]
    intro heq
    exact hpq (congrArg (fieldPoint τ) ((fieldPoint_injective σ) heq))
  · intro z hz hline
    obtain ⟨a, ha⟩ := hV z hz
    rw [← hp, ← hq, ← ha, embeddingPointMap_fieldPoint, embeddingPointMap_fieldPoint,
      embeddingPointMap_fieldPoint]
    apply fieldPoint_onAxis_transfer τ σ p q a hpq
    simpa only [hp, hq, ha, Triangle.edgeVector] using hline

def FieldTriangle.vertex {F : Type*} [Field F] (P : FieldTriangle F) (k : Fin 3) : F × F :=
  ![P.a, P.b, P.c] k

theorem FieldTriangle.realize_vertex {F : Type*} [Field F]
    (P : FieldTriangle F) (τ : F →+* ℝ) (k : Fin 3) :
    (P.realize τ).vertex k = fieldPoint τ (P.vertex k) := by
  fin_cases k <;> rfl

theorem FieldTriangle.realize_vertexImage {F : Type*} [Field F]
    (P : FieldTriangle F) (τ σ : F →+* ℝ) :
    (P.realize τ).VertexImage (P.realize σ) (embeddingPointMap τ σ) := by
  intro k
  rw [P.realize_vertex, P.realize_vertex, embeddingPointMap_fieldPoint]

theorem TriangleDissection.vertices_in_fieldPoint_range
    {F : Type*} [Field F] (τ : F →+* ℝ) {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (Q : Fin N → FieldTriangle F)
    (hQ : ∀ i : Fin N, T.tile i = (Q i).realize τ) :
    ∀ z ∈ T.vertexFinset, z ∈ Set.range (fieldPoint τ) := by
  intro z hz
  obtain ⟨i, k, hk⟩ := (T.mem_vertexFinset z).mp hz
  refine ⟨(Q i).vertex k, ?_⟩
  rw [← (Q i).realize_vertex, ← hQ i]
  exact hk

end Erdos633
