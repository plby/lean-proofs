import ErdosProblems.Erdos633.Congruence
import ErdosProblems.Erdos633.VertexGeometry
import ErdosProblems.Erdos633.FieldCoordinateMap

/-!
# Triangles under real embeddings of a coefficient field

Squared distances and signed double areas are polynomial expressions in
the coordinates. Their identities therefore survive every real embedding.
In particular, corresponding side congruences and a common signed-area
equation survive. Coverage and disjoint interiors are not assumed or
asserted here: these remain the geometric part of conjugating a tiling.
-/

namespace Erdos633

def fieldPoint {F : Type*} [Field F] (σ : F →+* ℝ) (p : F × F) : ℂ :=
  ⟨σ p.1, σ p.2⟩

def fieldSquaredDistance {F : Type*} [Field F] (p q : F × F) : F :=
  (q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2

def fieldDoubleArea {F : Type*} [Field F] (p q r : F × F) : F :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

theorem fieldPoint_injective {F : Type*} [Field F] (σ : F →+* ℝ) :
    Function.Injective (fieldPoint σ) := by
  intro p q h
  apply Prod.ext
  · exact σ.injective (congrArg Complex.re h)
  · exact σ.injective (congrArg Complex.im h)

theorem normSq_fieldPoint_sub {F : Type*} [Field F] (σ : F →+* ℝ) (p q : F × F) :
    Complex.normSq (fieldPoint σ q - fieldPoint σ p) = σ (fieldSquaredDistance p q) := by
  simp only [fieldPoint, fieldSquaredDistance, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, map_add, map_pow, map_sub]
  ring

theorem orientedDoubleArea_fieldPoint {F : Type*} [Field F] (σ : F →+* ℝ)
    (p q r : F × F) :
    orientedDoubleArea (fieldPoint σ p) (fieldPoint σ q) (fieldPoint σ r) =
      σ (fieldDoubleArea p q r) := by
  simp [fieldPoint, fieldDoubleArea, orientedDoubleArea, map_sub, map_mul]

structure FieldTriangle (F : Type*) [Field F] where
  a : F × F
  b : F × F
  c : F × F
  nondegenerate : fieldDoubleArea a b c ≠ 0

def FieldTriangle.realize {F : Type*} [Field F] (T : FieldTriangle F) (σ : F →+* ℝ) :
    Triangle where
  a := fieldPoint σ T.a
  b := fieldPoint σ T.b
  c := fieldPoint σ T.c
  nondegenerate := by
    change orientedDoubleArea (fieldPoint σ T.a) (fieldPoint σ T.b) (fieldPoint σ T.c) ≠ 0
    rw [orientedDoubleArea_fieldPoint]
    exact fun h => T.nondegenerate (σ.injective (h.trans σ.map_zero.symm))

theorem FieldTriangle.realize_doubleArea {F : Type*} [Field F]
    (T : FieldTriangle F) (σ : F →+* ℝ) :
    orientedDoubleArea (T.realize σ).a (T.realize σ).b (T.realize σ).c =
      σ (fieldDoubleArea T.a T.b T.c) := orientedDoubleArea_fieldPoint σ T.a T.b T.c

theorem fieldSquaredDistance_eq_of_embedding {F : Type*} [Field F]
    (τ : F →+* ℝ) (p q r s : F × F)
    (h : Complex.normSq (fieldPoint τ q - fieldPoint τ p) =
      Complex.normSq (fieldPoint τ s - fieldPoint τ r)) :
    fieldSquaredDistance p q = fieldSquaredDistance r s := by
  apply τ.injective
  simpa only [normSq_fieldPoint_sub] using h

theorem FieldTriangle.congruent_realize_of_normSq {F : Type*} [Field F]
    (P Q : FieldTriangle F) (τ σ : F →+* ℝ)
    (hab : Complex.normSq ((P.realize τ).b - (P.realize τ).a) =
      Complex.normSq ((Q.realize τ).b - (Q.realize τ).a))
    (hac : Complex.normSq ((P.realize τ).c - (P.realize τ).a) =
      Complex.normSq ((Q.realize τ).c - (Q.realize τ).a))
    (hbc : Complex.normSq ((P.realize τ).c - (P.realize τ).b) =
      Complex.normSq ((Q.realize τ).c - (Q.realize τ).b)) :
    ∃ e : ℂ ≃ᵢ ℂ, e '' (P.realize σ).carrier = (Q.realize σ).carrier := by
  apply Triangle.congruent_of_normSq
  · exact (normSq_fieldPoint_sub σ P.a P.b).trans
      ((congrArg σ (fieldSquaredDistance_eq_of_embedding τ P.a P.b Q.a Q.b hab)).trans
        (normSq_fieldPoint_sub σ Q.a Q.b).symm)
  · exact (normSq_fieldPoint_sub σ P.a P.c).trans
      ((congrArg σ (fieldSquaredDistance_eq_of_embedding τ P.a P.c Q.a Q.c hac)).trans
        (normSq_fieldPoint_sub σ Q.a Q.c).symm)
  · exact (normSq_fieldPoint_sub σ P.b P.c).trans
      ((congrArg σ (fieldSquaredDistance_eq_of_embedding τ P.b P.c Q.b Q.c hbc)).trans
        (normSq_fieldPoint_sub σ Q.b Q.c).symm)

theorem FieldTriangle.doubleArea_relation_transfer {F : Type*} [Field F]
    (P R : FieldTriangle F) (τ σ : F →+* ℝ) (N : ℕ)
    (h : orientedDoubleArea (P.realize τ).a (P.realize τ).b (P.realize τ).c =
      N * orientedDoubleArea (R.realize τ).a (R.realize τ).b (R.realize τ).c) :
    orientedDoubleArea (P.realize σ).a (P.realize σ).b (P.realize σ).c =
      N * orientedDoubleArea (R.realize σ).a (R.realize σ).b (R.realize σ).c := by
  have heq : fieldDoubleArea P.a P.b P.c = (N : F) * fieldDoubleArea R.a R.b R.c := by
    apply τ.injective
    simpa only [FieldTriangle.realize_doubleArea, map_mul, map_natCast] using h
  simpa only [FieldTriangle.realize_doubleArea, map_mul, map_natCast] using congrArg σ heq

def Triangle.CoordinatesIn (P : Triangle) (F : Subfield ℝ) : Prop :=
  ∀ k : Fin 3, (P.vertex k).re ∈ F ∧ (P.vertex k).im ∈ F

def Triangle.toFieldTriangle (P : Triangle) (F : Subfield ℝ) (h : P.CoordinatesIn F) :
    FieldTriangle F where
  a := (⟨P.a.re, (h 0).1⟩, ⟨P.a.im, (h 0).2⟩)
  b := (⟨P.b.re, (h 1).1⟩, ⟨P.b.im, (h 1).2⟩)
  c := (⟨P.c.re, (h 2).1⟩, ⟨P.c.im, (h 2).2⟩)
  nondegenerate := by
    intro hz
    apply P.nondegenerate
    have hcoe := congrArg (fun a : F => (a : ℝ)) hz
    simpa [fieldDoubleArea] using hcoe

theorem Triangle.toFieldTriangle_realize (P : Triangle) (F : Subfield ℝ)
    (h : P.CoordinatesIn F) : (P.toFieldTriangle F h).realize (algebraMap F ℝ) = P := by
  apply Triangle.ext <;> apply Complex.ext <;> rfl

end Erdos633
