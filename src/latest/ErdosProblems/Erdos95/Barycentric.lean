/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Finite barycentric subdivisions

This file gives a small finite-complex model tailored to the combinatorial
Borsuk--Ulam argument needed for Erdos 95.  Faces are nonempty finite sets.
The barycentric subdivision has the nonempty faces of the old complex as
vertices, and its faces are the nonempty chains under inclusion.
-/

namespace Erdos95.Barycentric

/-- A finite abstract simplicial complex, with all computational instances
stored explicitly so that the construction can be iterated. -/
structure FiniteComplex where
  Vertex : Type
  vertexFintype : Fintype Vertex
  vertexDecidableEq : DecidableEq Vertex
  IsFace : Finset Vertex → Prop
  isFaceDecidable : DecidablePred IsFace
  face_nonempty : ∀ {s}, IsFace s → s.Nonempty
  singleton_face : ∀ v, IsFace {v}
  face_of_nonempty_subset : ∀ {s t}, IsFace s → t ⊆ s → t.Nonempty → IsFace t

attribute [instance] FiniteComplex.vertexFintype
  FiniteComplex.vertexDecidableEq FiniteComplex.isFaceDecidable

/-- A vertex of the barycentric subdivision is a nonempty face of the old
complex. -/
abbrev BaryVertex (K : FiniteComplex) := {s : Finset K.Vertex // K.IsFace s}

/-- A finite set of old faces is a chain under inclusion. -/
def IsFaceChain (K : FiniteComplex) (S : Finset (BaryVertex K)) : Prop :=
  S.Nonempty ∧ ∀ A ∈ S, ∀ B ∈ S, A.1 ⊆ B.1 ∨ B.1 ⊆ A.1

noncomputable instance (K : FiniteComplex) : DecidablePred (IsFaceChain K) := by
  intro S
  classical
  infer_instance

/-- The barycentric subdivision of a finite complex. -/
noncomputable def barycentricSubdivision (K : FiniteComplex) : FiniteComplex where
  Vertex := BaryVertex K
  vertexFintype := inferInstance
  vertexDecidableEq := inferInstance
  IsFace := IsFaceChain K
  isFaceDecidable := inferInstance
  face_nonempty h := h.1
  singleton_face A := by
    refine ⟨Finset.singleton_nonempty A, ?_⟩
    intro B hB C hC
    simp only [Finset.mem_singleton] at hB hC
    subst B
    subst C
    exact Or.inl Finset.Subset.rfl
  face_of_nonempty_subset := by
    intro S T hS hTS hT
    refine ⟨hT, ?_⟩
    intro A hA B hB
    exact hS.2 A (hTS hA) B (hTS hB)

/-- The signed vertices of the boundary of the `d`-cross-polytope. -/
abbrev SignedAtom (d : ℕ) := Fin d × Bool

/-- The boundary complex of the cross-polytope: a face is a nonempty set of
signed coordinate vertices containing no opposite pair. -/
def crossPolytopeBoundary (d : ℕ) : FiniteComplex where
  Vertex := SignedAtom d
  vertexFintype := inferInstance
  vertexDecidableEq := inferInstance
  IsFace s := s.Nonempty ∧
    ∀ i : Fin d, ¬ ((i, false) ∈ s ∧ (i, true) ∈ s)
  isFaceDecidable := inferInstance
  face_nonempty h := h.1
  singleton_face v := by
    refine ⟨Finset.singleton_nonempty v, ?_⟩
    intro i hi
    simp only [Finset.mem_singleton] at hi
    have := hi.1.trans hi.2.symm
    simp at this
  face_of_nonempty_subset := by
    intro s t hs hts ht
    refine ⟨ht, ?_⟩
    intro i hi
    exact hs.2 i ⟨hts hi.1, hts hi.2⟩

/-- Every face of the `d`-cross-polytope boundary has at most `d` vertices. -/
theorem card_face_crossPolytopeBoundary_le (d : ℕ)
    {s : Finset (crossPolytopeBoundary d).Vertex}
    (hs : (crossPolytopeBoundary d).IsFace s) :
    s.card ≤ d := by
  have hinj : Set.InjOn Prod.fst
      (↑s : Set (crossPolytopeBoundary d).Vertex) := by
    rintro ⟨i, b⟩ hib ⟨j, c⟩ hjc hij
    simp only [Prod.fst] at hij
    subst j
    have hbc : b = c := by
      by_contra hbc
      have hbool : (b = false ∧ c = true) ∨ (c = false ∧ b = true) := by
        cases b <;> cases c <;> simp_all
      rcases hbool with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hs.2 i ⟨hib, hjc⟩
      · exact hs.2 i ⟨hjc, hib⟩
    exact Prod.ext rfl hbc
  calc
    s.card = (s.image Prod.fst).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_le_card (by simp)
    _ = d := by simp

/-- Barycentric subdivision preserves an a priori face-cardinality bound.
The rank of a vertex in a chain is the cardinality of the old face. -/
theorem card_face_barycentricSubdivision_le
    (K : FiniteComplex) (d : ℕ)
    (hK : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    {S : Finset (barycentricSubdivision K).Vertex}
    (hS : (barycentricSubdivision K).IsFace S) :
    S.card ≤ d := by
  let rank : BaryVertex K → Fin d := fun A ↦
    ⟨A.1.card - 1, by
      have hpos : 0 < A.1.card := Finset.card_pos.mpr (K.face_nonempty A.2)
      have hle : A.1.card ≤ d := hK A.2
      omega⟩
  have hinj : Set.InjOn rank
      (↑S : Set (barycentricSubdivision K).Vertex) := by
    intro A hA B hB hab
    apply Subtype.ext
    have hcard : A.1.card = B.1.card := by
      have hApos : 0 < A.1.card := Finset.card_pos.mpr (K.face_nonempty A.2)
      have hBpos : 0 < B.1.card := Finset.card_pos.mpr (K.face_nonempty B.2)
      have hval := congrArg Fin.val hab
      dsimp [rank] at hval
      omega
    rcases hS.2 A hA B hB with hAB | hBA
    · exact Finset.eq_of_subset_of_card_le hAB hcard.ge
    · exact (Finset.eq_of_subset_of_card_le hBA hcard.le).symm
  calc
    S.card = (S.image rank).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_le_card (by simp)
    _ = d := by simp

/-- Repeated barycentric subdivision of the cross-polytope boundary. -/
noncomputable def iteratedBoundary (d : ℕ) : ℕ → FiniteComplex
  | 0 => crossPolytopeBoundary d
  | r + 1 => barycentricSubdivision (iteratedBoundary d r)

/-- Every face in every iterated subdivision still has at most `d` vertices. -/
theorem card_face_iteratedBoundary_le (d r : ℕ)
    {s : Finset (iteratedBoundary d r).Vertex}
    (hs : (iteratedBoundary d r).IsFace s) :
    s.card ≤ d := by
  induction r with
  | zero => exact card_face_crossPolytopeBoundary_le d hs
  | succ r ih =>
      exact card_face_barycentricSubdivision_le (iteratedBoundary d r) d
        (fun {s} h ↦ ih (s := s) h) hs

/-! ## Antipodal actions -/

/-- An involution of the vertices of a finite complex which preserves its
faces.  The inverse implication for faces follows from involutivity. -/
structure ComplexInvolution (K : FiniteComplex) where
  neg : K.Vertex → K.Vertex
  neg_neg : ∀ v, neg (neg v) = v
  face_neg : ∀ {s}, K.IsFace s → K.IsFace (s.image neg)

namespace ComplexInvolution

variable {K : FiniteComplex} (A : ComplexInvolution K)

theorem neg_injective : Function.Injective A.neg := by
  intro v w h
  simpa only [A.neg_neg] using congrArg A.neg h

theorem image_neg_image_neg (s : Finset K.Vertex) :
    (s.image A.neg).image A.neg = s := by
  ext v
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    simpa only [A.neg_neg] using hu
  · intro hv
    exact ⟨A.neg v, ⟨v, hv, rfl⟩, A.neg_neg v⟩

theorem face_neg_iff {s : Finset K.Vertex} :
    K.IsFace (s.image A.neg) ↔ K.IsFace s := by
  constructor
  · intro hs
    simpa only [A.image_neg_image_neg] using A.face_neg hs
  · exact A.face_neg

/-- An involution of a complex induces one on its barycentric subdivision. -/
noncomputable def barycentricLift :
    ComplexInvolution (barycentricSubdivision K) where
  neg F := ⟨F.1.image A.neg, A.face_neg F.2⟩
  neg_neg F := by
    apply Subtype.ext
    exact A.image_neg_image_neg F.1
  face_neg := by
    intro S hS
    refine ⟨Finset.image_nonempty.mpr hS.1, ?_⟩
    intro F hF G hG
    rcases Finset.mem_image.mp hF with ⟨F₀, hF₀, rfl⟩
    rcases Finset.mem_image.mp hG with ⟨G₀, hG₀, rfl⟩
    rcases hS.2 F₀ hF₀ G₀ hG₀ with hFG | hGF
    · left
      exact Finset.image_mono _ hFG
    · right
      exact Finset.image_mono _ hGF

end ComplexInvolution

/-- Coordinate-sign reversal on the cross-polytope boundary. -/
def crossPolytopeAntipode (d : ℕ) :
    ComplexInvolution (crossPolytopeBoundary d) where
  neg v := (v.1, !v.2)
  neg_neg v := by cases v with | mk i b => cases b <;> rfl
  face_neg := by
    intro s hs
    refine ⟨Finset.image_nonempty.mpr hs.1, ?_⟩
    intro i hi
    apply hs.2 i
    constructor
    · rcases Finset.mem_image.mp hi.2 with ⟨v, hv, huv⟩
      cases v with
      | mk j b =>
          cases b
          · have hji : j = i := congrArg Prod.fst huv
            subst j
            exact hv
          · simp at huv
    · rcases Finset.mem_image.mp hi.1 with ⟨v, hv, huv⟩
      cases v with
      | mk j b =>
          cases b
          · simp at huv
          · have hji : j = i := congrArg Prod.fst huv
            subst j
            exact hv

/-- The recursively induced antipodal action on every iterated subdivision. -/
noncomputable def iteratedAntipode (d : ℕ) :
    ∀ r, ComplexInvolution (iteratedBoundary d r)
  | 0 => crossPolytopeAntipode d
  | r + 1 => (iteratedAntipode d r).barycentricLift

@[simp] theorem iteratedAntipode_zero_neg (d : ℕ) (v : SignedAtom d) :
    (iteratedAntipode d 0).neg v = (v.1, !v.2) := rfl

@[simp] theorem iteratedAntipode_succ_neg (d r : ℕ)
    (F : (iteratedBoundary d (r + 1)).Vertex) :
    (iteratedAntipode d (r + 1)).neg F =
      ⟨F.1.image (iteratedAntipode d r).neg,
        (iteratedAntipode d r).face_neg F.2⟩ := rfl

/-! ## Geometric realization -/

/-- The signed coordinate vector associated with a cross-polytope vertex. -/
def signedBasisVector {d : ℕ} (v : SignedAtom d) : Fin d → ℝ :=
  fun j ↦ if j = v.1 then if v.2 then 1 else -1 else 0

theorem signedBasisVector_antipode {d : ℕ} (v : SignedAtom d) :
    signedBasisVector (v.1, !v.2) = -signedBasisVector v := by
  rcases v with ⟨i, b⟩
  funext j
  by_cases hj : j = i
  · subst j
    cases b <;> simp [signedBasisVector]
  · cases b <;> simp [signedBasisVector, hj]

/-- Arithmetic barycenter of a nonempty finite face. -/
noncomputable def faceAverage {K : FiniteComplex} {E : Type*}
    [AddCommGroup E] [Module ℝ E] (f : K.Vertex → E) (F : BaryVertex K) : E :=
  (F.1.card : ℝ)⁻¹ • ∑ v ∈ F.1, f v

/-- Realization of an iterated barycentric vertex.  At each successor stage
the new vertex is sent to the barycenter of the old face it represents. -/
noncomputable def realize (d : ℕ) :
    ∀ r, (iteratedBoundary d r).Vertex → (Fin d → ℝ)
  | 0 => signedBasisVector
  | r + 1 => faceAverage (realize d r)

@[simp] theorem realize_zero (d : ℕ) (v : SignedAtom d) :
    realize d 0 v = signedBasisVector v := rfl

@[simp] theorem realize_succ (d r : ℕ)
    (F : (iteratedBoundary d (r + 1)).Vertex) :
    realize d (r + 1) F = faceAverage (realize d r) F := rfl

theorem faceAverage_image_involution
    {K : FiniteComplex} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : ComplexInvolution K) (f : K.Vertex → E)
    (hf : ∀ v, f (A.neg v) = -f v) (F : BaryVertex K) :
    faceAverage f ⟨F.1.image A.neg, A.face_neg F.2⟩ = -faceAverage f F := by
  have hcard : (F.1.image A.neg).card = F.1.card :=
    Finset.card_image_iff.mpr A.neg_injective.injOn
  have hsum : (∑ v ∈ F.1.image A.neg, f v) = -∑ v ∈ F.1, f v := by
    rw [Finset.sum_image]
    · simp_rw [hf]
      exact Finset.sum_neg_distrib (s := F.1) f
    · exact A.neg_injective.injOn
  simp only [faceAverage, hcard, hsum, smul_neg]

/-- The geometric realization intertwines the combinatorial antipode with
vector negation at every subdivision level. -/
theorem realize_antipode (d r : ℕ) (v : (iteratedBoundary d r).Vertex) :
    realize d r ((iteratedAntipode d r).neg v) = -realize d r v := by
  induction r with
  | zero => exact signedBasisVector_antipode v
  | succ r ih =>
      exact faceAverage_image_involution (iteratedAntipode d r)
        (realize d r) (fun w ↦ ih w) v

/-! ## Quantitative mesh estimates -/

/-- A uniform bound for the diameter of every face in a realization. -/
def FaceDiameter (K : FiniteComplex) {E : Type*} [PseudoMetricSpace E]
    (f : K.Vertex → E) (D : ℝ) : Prop :=
  ∀ ⦃s : Finset K.Vertex⦄, K.IsFace s →
    ∀ ⦃v⦄, v ∈ s → ∀ ⦃w⦄, w ∈ s → dist (f v) (f w) ≤ D

/-- The barycenter of a face is at distance at most its diameter from every
point of any containing face. -/
theorem norm_faceAverage_sub_le
    {K : FiniteComplex} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : K.Vertex → E) (D : ℝ) (F G : BaryVertex K)
    (hFG : F.1 ⊆ G.1)
    (hD : ∀ ⦃v⦄, v ∈ G.1 → ∀ ⦃w⦄, w ∈ G.1 → ‖f v - f w‖ ≤ D)
    {y : K.Vertex} (hy : y ∈ G.1) :
    ‖faceAverage f F - f y‖ ≤ D := by
  have hFpos : 0 < F.1.card := Finset.card_pos.mpr (K.face_nonempty F.2)
  have hFne : (F.1.card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hFpos)
  have hFinv : 0 ≤ (F.1.card : ℝ)⁻¹ :=
    le_of_lt (inv_pos.mpr (by exact_mod_cast hFpos))
  have havg :
      faceAverage f F - f y =
        (F.1.card : ℝ)⁻¹ • ∑ x ∈ F.1, (f x - f y) := by
    unfold faceAverage
    rw [Finset.sum_sub_distrib, Finset.sum_const,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_sub, smul_smul,
      inv_mul_cancel₀ hFne, one_smul]
  rw [havg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hFinv]
  calc
    (F.1.card : ℝ)⁻¹ * ‖∑ x ∈ F.1, (f x - f y)‖
        ≤ (F.1.card : ℝ)⁻¹ * ∑ x ∈ F.1, ‖f x - f y‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le F.1 fun x ↦ f x - f y) hFinv
    _ ≤ (F.1.card : ℝ)⁻¹ * ∑ _x ∈ F.1, D := by
      gcongr with x hx
      exact hD (hFG hx) hy
    _ = D := by
      rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]
      simp [smul_eq_mul, hFne]

/-- Quantitative form of the nested-barycenter estimate.  The common points
cancel, so only the vertices in `G \ F` contribute. -/
theorem norm_faceAverage_sub_faceAverage_le
    {K : FiniteComplex} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : K.Vertex → E) (D : ℝ) (F G : BaryVertex K)
    (hFG : F.1 ⊆ G.1)
    (hD : ∀ ⦃v⦄, v ∈ G.1 → ∀ ⦃w⦄, w ∈ G.1 → ‖f v - f w‖ ≤ D) :
    ‖faceAverage f F - faceAverage f G‖ ≤
      ((G.1 \ F.1).card : ℝ) / G.1.card * D := by
  have hFpos : 0 < F.1.card := Finset.card_pos.mpr (K.face_nonempty F.2)
  have hGpos : 0 < G.1.card := Finset.card_pos.mpr (K.face_nonempty G.2)
  have hFne : (F.1.card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hFpos)
  have hGne : (G.1.card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hGpos)
  have hGinv : 0 ≤ (G.1.card : ℝ)⁻¹ :=
    le_of_lt (inv_pos.mpr (by exact_mod_cast hGpos))
  have hsumF : (F.1.card : ℝ) • faceAverage f F = ∑ x ∈ F.1, f x := by
    unfold faceAverage
    rw [smul_smul, mul_inv_cancel₀ hFne, one_smul]
  have hsumG : (G.1.card : ℝ) • faceAverage f G = ∑ x ∈ G.1, f x := by
    unfold faceAverage
    rw [smul_smul, mul_inv_cancel₀ hGne, one_smul]
  have hcardNat := Finset.card_sdiff_add_card_eq_card hFG
  have hcardReal :
      (G.1.card : ℝ) = (G.1 \ F.1).card + F.1.card := by
    exact_mod_cast hcardNat.symm
  have hsumSplit := Finset.sum_sdiff (f := f) hFG
  have hid :
      faceAverage f F - faceAverage f G =
        (G.1.card : ℝ)⁻¹ •
          ∑ y ∈ G.1 \ F.1, (faceAverage f F - f y) := by
    apply (smul_right_injective E hGne)
    change (G.1.card : ℝ) • (faceAverage f F - faceAverage f G) =
      (G.1.card : ℝ) • ((G.1.card : ℝ)⁻¹ •
        ∑ y ∈ G.1 \ F.1, (faceAverage f F - f y))
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hGne, one_smul,
      Finset.sum_sub_distrib, Finset.sum_const,
      ← Nat.cast_smul_eq_nsmul ℝ]
    rw [hsumG, hcardReal, add_smul, hsumF]
    rw [← hsumSplit]
    abel
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_nonneg hGinv]
  calc
    (G.1.card : ℝ)⁻¹ *
          ‖∑ y ∈ G.1 \ F.1, (faceAverage f F - f y)‖
        ≤ (G.1.card : ℝ)⁻¹ *
          ∑ y ∈ G.1 \ F.1, ‖faceAverage f F - f y‖ :=
      mul_le_mul_of_nonneg_left
        (norm_sum_le (G.1 \ F.1) fun y ↦ faceAverage f F - f y) hGinv
    _ ≤ (G.1.card : ℝ)⁻¹ * ∑ _y ∈ G.1 \ F.1, D := by
      gcongr with y hy
      exact norm_faceAverage_sub_le f D F G hFG hD (Finset.mem_sdiff.mp hy).1
    _ = ((G.1 \ F.1).card : ℝ) / G.1.card * D := by
      rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]
      simp only [smul_eq_mul, div_eq_mul_inv]
      ring

theorem card_sdiff_div_le_contraction
    {α : Type*} [DecidableEq α] {F G : Finset α} {d : ℕ}
    (hF : F.Nonempty) (hFG : F ⊆ G) (hGd : G.card ≤ d) (hd : 0 < d) :
    ((G \ F).card : ℝ) / G.card ≤ 1 - 1 / d := by
  have hFpos : 0 < F.card := Finset.card_pos.mpr hF
  have hGpos : 0 < G.card := lt_of_lt_of_le hFpos (Finset.card_le_card hFG)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hGR : (0 : ℝ) < G.card := by exact_mod_cast hGpos
  have hprodNat : G.card ≤ F.card * d := by
    calc
      G.card ≤ d := hGd
      _ ≤ F.card * d := by nlinarith
  have hprod : (G.card : ℝ) ≤ F.card * d := by exact_mod_cast hprodNat
  have hinv : (1 : ℝ) / d ≤ F.card / G.card := by
    rw [div_le_div_iff₀ hdR hGR]
    simpa using hprod
  have hcardNat := Finset.card_sdiff_add_card_eq_card hFG
  have hcard : ((G \ F).card : ℝ) + F.card = G.card := by
    exact_mod_cast hcardNat
  have hratio : ((G \ F).card : ℝ) / G.card = 1 - F.card / G.card := by
    field_simp
    linarith
  rw [hratio]
  exact sub_le_sub_left hinv 1

/-- One barycentric subdivision shrinks every face diameter by at least the
factor `1 - 1/d` when old faces have at most `d` vertices. -/
theorem faceDiameter_barycentricSubdivision
    (K : FiniteComplex) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : K.Vertex → E) (D : ℝ) (d : ℕ) (hd : 0 < d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (hdiam : FaceDiameter K f D) :
    FaceDiameter (barycentricSubdivision K) (faceAverage f)
      ((1 - 1 / (d : ℝ)) * D) := by
  intro S hS F hFS G hGS
  have hDnonneg : 0 ≤ D := by
    obtain ⟨x, hx⟩ := K.face_nonempty G.2
    simpa using hdiam G.2 hx hx
  rcases hS.2 F hFS G hGS with hFG | hGF
  · rw [dist_eq_norm]
    calc
      ‖faceAverage f F - faceAverage f G‖
          ≤ ((G.1 \ F.1).card : ℝ) / G.1.card * D :=
        norm_faceAverage_sub_faceAverage_le f D F G hFG
          (fun hv hhv hw hhw ↦ by
            simpa [dist_eq_norm] using hdiam G.2 hhv hhw)
      _ ≤ (1 - 1 / (d : ℝ)) * D :=
        mul_le_mul_of_nonneg_right
          (card_sdiff_div_le_contraction
            (K.face_nonempty F.2) hFG (hcard G.2) hd) hDnonneg
  · rw [dist_comm, dist_eq_norm]
    calc
      ‖faceAverage f G - faceAverage f F‖
          ≤ ((F.1 \ G.1).card : ℝ) / F.1.card * D :=
        norm_faceAverage_sub_faceAverage_le f D G F hGF
          (fun hv hhv hw hhw ↦ by
            simpa [dist_eq_norm] using hdiam F.2 hhv hhw)
      _ ≤ (1 - 1 / (d : ℝ)) * D :=
        mul_le_mul_of_nonneg_right
          (card_sdiff_div_le_contraction
            (K.face_nonempty G.2) hGF (hcard F.2) hd) hDnonneg

theorem norm_signedBasisVector_le_one {d : ℕ} (v : SignedAtom d) :
    ‖signedBasisVector v‖ ≤ 1 := by
  rcases v with ⟨i, b⟩
  rw [Pi.norm_def]
  norm_cast
  apply Finset.sup_le
  intro j hj
  by_cases h : j = i
  · subst j
    cases b <;> simp [signedBasisVector]
  · cases b <;> simp [signedBasisVector, h]

theorem faceDiameter_crossPolytope (d : ℕ) :
    FaceDiameter (crossPolytopeBoundary d) signedBasisVector 2 := by
  intro s hs v hv w hw
  calc
    dist (signedBasisVector v) (signedBasisVector w)
        ≤ ‖signedBasisVector v‖ + ‖signedBasisVector w‖ :=
      dist_le_norm_add_norm _ _
    _ ≤ 1 + 1 := add_le_add
      (norm_signedBasisVector_le_one v) (norm_signedBasisVector_le_one w)
    _ = 2 := by norm_num

/-- Explicit exponentially decaying mesh bound for the iterated realization. -/
theorem faceDiameter_realize (d : ℕ) (hd : 0 < d) (r : ℕ) :
    FaceDiameter (iteratedBoundary d r) (realize d r)
      (2 * (1 - 1 / (d : ℝ)) ^ r) := by
  induction r with
  | zero =>
      simpa [iteratedBoundary, realize] using faceDiameter_crossPolytope d
  | succ r ih =>
      have h := faceDiameter_barycentricSubdivision
        (iteratedBoundary d r) (realize d r)
        (2 * (1 - 1 / (d : ℝ)) ^ r) d hd
        (fun {s} hs ↦ card_face_iteratedBoundary_le d r hs) ih
      change FaceDiameter (barycentricSubdivision (iteratedBoundary d r))
        (faceAverage (realize d r))
        (2 * (1 - 1 / (d : ℝ)) ^ (r + 1))
      convert h using 1 <;> rw [pow_succ] <;> ring

/-- Faces in sufficiently deep subdivisions have arbitrarily small diameter. -/
theorem exists_iteratedBoundary_faceDiameter_lt
    (d : ℕ) (hd : 0 < d) {ε : ℝ} (hε : 0 < ε) :
    ∃ r, ∀ ⦃s : Finset (iteratedBoundary d r).Vertex⦄,
      (iteratedBoundary d r).IsFace s →
        ∀ ⦃v⦄, v ∈ s → ∀ ⦃w⦄, w ∈ s →
          dist (realize d r v) (realize d r w) < ε := by
  let q : ℝ := 1 - 1 / d
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hq0 : 0 ≤ q := by
    dsimp [q]
    have : (1 : ℝ) / d ≤ 1 := by
      rw [div_le_one hdR]
      exact_mod_cast hd
    linarith
  have hq1 : q < 1 := by
    dsimp [q]
    have : (0 : ℝ) < 1 / d := div_pos zero_lt_one hdR
    linarith
  have htend : Filter.Tendsto (fun r : ℕ ↦ 2 * q ^ r) Filter.atTop (nhds 0) := by
    convert (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1) :
        Filter.Tendsto (fun r : ℕ ↦ (2 : ℝ) * q ^ r)
          Filter.atTop (nhds ((2 : ℝ) * 0))) using 1 <;> norm_num
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨r, hr⟩ := htend ε hε
  refine ⟨r, ?_⟩
  intro s hs v hv w hw
  have hr' := hr r le_rfl
  have hnonneg : 0 ≤ 2 * q ^ r := mul_nonneg (by norm_num) (pow_nonneg hq0 r)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hr'
  exact lt_of_le_of_lt (faceDiameter_realize d hd r hs hv hw) (by
    simpa [q] using hr')

/-! ## Separation from the origin -/

/-- A finite chain has a largest member.  We select a member of maximal
cardinality and use comparability to turn the cardinality inequality into
inclusion. -/
theorem exists_chain_largest
    {K : FiniteComplex} {S : Finset (BaryVertex K)}
    (hS : IsFaceChain K S) :
    ∃ M ∈ S, ∀ F ∈ S, F.1 ⊆ M.1 := by
  obtain ⟨M, hMS, hMmax⟩ := Finset.exists_max_image S (fun F ↦ F.1.card) hS.1
  refine ⟨M, hMS, ?_⟩
  intro F hFS
  rcases hS.2 F hFS M hMS with hFM | hMF
  · exact hFM
  · have hcard : F.1.card ≤ M.1.card := hMmax F hFS
    have heq : M.1 = F.1 := Finset.eq_of_subset_of_card_le hMF hcard
    simpa [heq]

/-- Base separation for a face of the cross-polytope boundary. -/
theorem face_separated_crossPolytope (d : ℕ)
    {s : Finset (crossPolytopeBoundary d).Vertex}
    (hs : (crossPolytopeBoundary d).IsFace s) :
    ∃ L : (Fin d → ℝ) →ₗ[ℝ] ℝ, ∀ v ∈ s, L (signedBasisVector v) = 1 := by
  classical
  let sign : Fin d → ℝ := fun i ↦ if (i, true) ∈ s then 1 else -1
  let L : (Fin d → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x ↦ ∑ i, sign i * x i
      map_add' := by
        intro x y
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a x
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        change sign i * (a * x i) = a * (sign i * x i)
        ring }
  refine ⟨L, ?_⟩
  rintro ⟨i, b⟩ hv
  have hnotOpp : (i, !b) ∉ s := by
    intro hopp
    cases b
    · exact hs.2 i ⟨hv, hopp⟩
    · exact hs.2 i ⟨hopp, hv⟩
  cases b
  · have htrue : (i, true) ∉ s := by simpa using hnotOpp
    change (∑ j : Fin d, sign j * signedBasisVector (i, false) j) = 1
    rw [Finset.sum_eq_single i]
    · simp [sign, signedBasisVector, htrue]
    · intro j hj hji
      simp [signedBasisVector, hji]
    · simp
  · change (∑ j : Fin d, sign j * signedBasisVector (i, true) j) = 1
    rw [Finset.sum_eq_single i]
    · have hsign : sign i = 1 := by
        exact if_pos hv
      rw [hsign]
      simp [signedBasisVector]
    · intro j hj hji
      simp [signedBasisVector, hji]
    · simp

/-- Every face is contained in an affine hyperplane not passing through the
origin: one linear functional takes the constant value `1` on all its
realized vertices. -/
theorem face_separated_realize (d r : ℕ)
    {s : Finset (iteratedBoundary d r).Vertex}
    (hs : (iteratedBoundary d r).IsFace s) :
    ∃ L : (Fin d → ℝ) →ₗ[ℝ] ℝ, ∀ v ∈ s, L (realize d r v) = 1 := by
  classical
  induction r with
  | zero =>
      exact face_separated_crossPolytope d hs
  | succ r ih =>
      obtain ⟨M, hMs, hlargest⟩ := exists_chain_largest hs
      obtain ⟨L, hL⟩ := ih M.2
      refine ⟨L, ?_⟩
      intro F hFs
      have hFM : F.1 ⊆ M.1 := hlargest F hFs
      have hFpos : 0 < F.1.card := Finset.card_pos.mpr
        ((iteratedBoundary d r).face_nonempty F.2)
      have hFne : (F.1.card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hFpos)
      change L (faceAverage (realize d r) F) = 1
      unfold faceAverage
      rw [LinearMapClass.map_smul, map_sum]
      have hsum : (∑ x ∈ F.1, L (realize d r x)) = ∑ _x ∈ F.1, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hL x (hFM hx)
      rw [hsum, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_eq_mul]
      simpa [smul_eq_mul] using inv_mul_cancel₀ hFne

/-- In particular no realized subdivision vertex is the zero coefficient
vector. -/
theorem realize_ne_zero (d r : ℕ) (v : (iteratedBoundary d r).Vertex) :
    realize d r v ≠ 0 := by
  intro hv
  obtain ⟨L, hL⟩ := face_separated_realize d r
    ((iteratedBoundary d r).singleton_face v)
  have := hL v (by simp)
  rw [hv, map_zero] at this
  norm_num at this

end Erdos95.Barycentric
