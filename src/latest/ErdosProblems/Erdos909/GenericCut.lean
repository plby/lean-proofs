/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Baire.Lemmas

/-!
# Generic hyperplane cuts

This file contains the finite-family linear-algebra lemma used in the
Anderson--Keisler sphere-cutting construction.  If a parent direction `B` is
transverse to each pattern direction `D i`, then a generic normal vector in
`B` cuts `B` by one dimension without destroying any of those transversality
conditions.
-/

open Set Topology

namespace Erdos909.GenericCut

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The vectors in `B` which are orthogonal to the whole of `I`. -/
noncomputable def badNormal (B I : Submodule ℝ E) : Submodule ℝ B :=
  (Iᗮ).comap B.subtype

@[simp]
theorem mem_badNormal {B I : Submodule ℝ E} (v : B) :
    v ∈ badNormal B I ↔ ∀ w ∈ I, inner ℝ w (v : E) = 0 :=
  I.mem_orthogonal (v : E)

/-- If `I` is a nonzero subspace of `B`, the vectors of `B` orthogonal to
`I` form a proper subspace of `B`. -/
theorem badNormal_ne_top {B I : Submodule ℝ E} (hIB : I ≤ B) (hI : I ≠ ⊥) :
    badNormal B I ≠ ⊤ := by
  letI : Nontrivial I := Submodule.nontrivial_iff_ne_bot.mpr hI
  obtain ⟨z, hz⟩ := exists_ne (0 : I)
  intro htop
  have hzbad : (⟨z, hIB z.property⟩ : B) ∈ badNormal B I := by
    rw [htop]
    exact Submodule.mem_top
  have hzero := (mem_badNormal (⟨z, hIB z.property⟩ : B)).mp hzbad z z.property
  exact hz (Subtype.ext (inner_self_eq_zero.mp hzero))

/-- The complement of a proper real subspace is dense.  This formulation
does not require finite-dimensionality. -/
theorem dense_compl_submodule_of_ne_top {F : Type*} [TopologicalSpace F]
    [AddCommGroup F] [Module ℝ F] [ContinuousAdd F] [ContinuousSMul ℝ F]
    (p : Submodule ℝ F) (hp : p ≠ ⊤) :
    Dense ((p : Set F)ᶜ) := by
  rw [← interior_eq_empty_iff_dense_compl]
  by_contra hinterior
  have hn : (interior (p : Set F)).Nonempty := Set.nonempty_iff_ne_empty.mpr hinterior
  exact hp (p.eq_top_of_nonempty_interior' hn)

/-- There is a single vector in `B` simultaneously nonorthogonal to every
member of a finite family of nonzero subspaces of `B`. -/
theorem exists_goodNormal [Finite ι] (B : Submodule ℝ E)
    (I : ι → Submodule ℝ E) (hIB : ∀ i, I i ≤ B) (hI : ∀ i, I i ≠ ⊥) :
    ∃ v : B, ∀ i, v ∉ badNormal B (I i) := by
  apply Submodule.exists_forall_notMem_of_forall_ne_top
  exact fun i ↦ badNormal_ne_top (hIB i) (hI i)

/-- In a finite-dimensional parent direction, the simultaneous good normals
form a dense set. -/
theorem dense_goodNormals [Finite ι] [FiniteDimensional ℝ E]
    (B : Submodule ℝ E) (I : ι → Submodule ℝ E)
    (hIB : ∀ i, I i ≤ B) (hI : ∀ i, I i ≠ ⊥) :
    Dense {v : B | ∀ i, v ∉ badNormal B (I i)} := by
  letI : CompleteSpace B := FiniteDimensional.complete ℝ B
  have hopen : ∀ i, IsOpen ((badNormal B (I i) : Set B)ᶜ) := fun i ↦
    (Submodule.closed_of_finiteDimensional (badNormal B (I i))).isOpen_compl
  have hdense : ∀ i, Dense ((badNormal B (I i) : Set B)ᶜ) := fun i ↦
    dense_compl_submodule_of_ne_top _ (badNormal_ne_top (hIB i) (hI i))
  rw [show {v : B | ∀ i, v ∉ badNormal B (I i)} =
      ⋂ i, (badNormal B (I i) : Set B)ᶜ by
    ext v
    simp]
  exact dense_iInter_of_isOpen hopen hdense

/-- A countable dense family of simultaneously good normals can be selected.
This is the form needed to enumerate a countable cutting basis. -/
theorem exists_countable_dense_goodNormals [Finite ι] [FiniteDimensional ℝ E]
    (B : Submodule ℝ E) (I : ι → Submodule ℝ E)
    (hIB : ∀ i, I i ≤ B) (hI : ∀ i, I i ≠ ⊥) :
    ∃ s : Set B, s.Countable ∧ Dense s ∧
      s ⊆ {v : B | ∀ i, v ∉ badNormal B (I i)} := by
  obtain ⟨s, hs, hsc, hsd⟩ :=
    (dense_goodNormals B I hIB hI).exists_countable_dense_subset
  exact ⟨s, hsc, hsd, hs⟩

/-- Cutting a transverse subspace by a hyperplane whose normal is not
orthogonal to the old intersection preserves transversality. -/
theorem sup_inf_orthogonal_eq_top
    (B D : Submodule ℝ E) (hBD : D ⊔ B = ⊤) {v : E}
    (hv : v ∉ (D ⊓ B)ᗮ) :
    D ⊔ (B ⊓ (ℝ ∙ v)ᗮ) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  have hx : x ∈ D ⊔ B := by rw [hBD]; exact Submodule.mem_top
  rcases Submodule.mem_sup.mp hx with ⟨d, hd, b, hb, rfl⟩
  rw [Submodule.mem_orthogonal] at hv
  push Not at hv
  obtain ⟨z, ⟨hzD, hzB⟩, hzv⟩ := hv
  let a : ℝ := (inner ℝ z v)⁻¹ * inner ℝ b v
  have hzv' : inner ℝ z v ≠ 0 := hzv
  have hcut : b - a • z ∈ B ⊓ (ℝ ∙ v)ᗮ := by
    refine ⟨B.sub_mem hb (B.smul_mem a hzB), ?_⟩
    apply Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
    simp only [inner_sub_left, inner_smul_left, starRingEnd_apply, star_trivial, a]
    field_simp
    simp
  have hD : d + a • z ∈ D := D.add_mem hd (D.smul_mem a hzD)
  convert Submodule.add_mem_sup hD hcut using 1 <;> module

/-- For a finite family of pattern directions, generic normals inside `B`
preserve every transversality equation simultaneously. -/
theorem dense_normals_preserving_transversality
    [Finite ι] [FiniteDimensional ℝ E]
    (B : Submodule ℝ E) (D : ι → Submodule ℝ E)
    (htrans : ∀ i, D i ⊔ B = ⊤) (hinter : ∀ i, D i ⊓ B ≠ ⊥) :
    Dense {v : B | ∀ i, D i ⊔ (B ⊓ (ℝ ∙ (v : E))ᗮ) = ⊤} := by
  apply (dense_goodNormals B (fun i ↦ D i ⊓ B) (fun _ ↦ inf_le_right) hinter).mono
  intro v hv i
  apply sup_inf_orthogonal_eq_top B (D i) (htrans i)
  simpa only [badNormal, Submodule.mem_comap, Submodule.subtype_apply] using hv i

/-- Existence-only version of
`dense_normals_preserving_transversality`, requiring no topology or
finite-dimensionality. -/
theorem exists_normal_preserving_transversality [Finite ι]
    (B : Submodule ℝ E) (D : ι → Submodule ℝ E)
    (htrans : ∀ i, D i ⊔ B = ⊤) (hinter : ∀ i, D i ⊓ B ≠ ⊥) :
    ∃ v : B, ∀ i, D i ⊔ (B ⊓ (ℝ ∙ (v : E))ᗮ) = ⊤ := by
  obtain ⟨v, hv⟩ := exists_goodNormal B (fun i ↦ D i ⊓ B)
    (fun _ ↦ inf_le_right) hinter
  refine ⟨v, fun i ↦ sup_inf_orthogonal_eq_top B (D i) (htrans i) ?_⟩
  simpa only [badNormal, Submodule.mem_comap, Submodule.subtype_apply] using hv i

section Affine

/-- The affine child cut through `p`, inside the parent affine subspace `A`,
with normal `v`.  The scalar offset of a chord cut chooses `p`; only `v`
controls its direction. -/
noncomputable def childCut (A : AffineSubspace ℝ E) (p v : E) :
    AffineSubspace ℝ E :=
  AffineSubspace.mk' p (A.direction ⊓ (ℝ ∙ v)ᗮ)

@[simp]
theorem childCut_direction (A : AffineSubspace ℝ E) (p v : E) :
    (childCut A p v).direction = A.direction ⊓ (ℝ ∙ v)ᗮ :=
  AffineSubspace.direction_mk' _ _

/-- A cut through a point of its parent is an affine subspace of that
parent. -/
theorem childCut_le (A : AffineSubspace ℝ E) {p v : E} (hp : p ∈ A) :
    childCut A p v ≤ A := by
  have h : childCut A p v ≤ AffineSubspace.mk' p A.direction := by
    exact (AffineSubspace.mk'_le_mk'_iff p).mpr inf_le_left
  rwa [AffineSubspace.mk'_eq hp] at h

/-- Affine wrapper around `sup_inf_orthogonal_eq_top`: a generic child cut
retains transversality to a pattern direction. -/
theorem childCut_transverse (A : AffineSubspace ℝ E) (D : Submodule ℝ E)
    {p v : E} (htrans : D ⊔ A.direction = ⊤) (hv : v ∉ (D ⊓ A.direction)ᗮ) :
    D ⊔ (childCut A p v).direction = ⊤ := by
  rw [childCut_direction]
  exact sup_inf_orthogonal_eq_top A.direction D htrans hv

/-- For finitely many pattern directions, the normals in an affine parent's
direction which give transverse child cuts are dense. -/
theorem dense_affine_childCut_normals [Finite ι] [FiniteDimensional ℝ E]
    (A : AffineSubspace ℝ E) (D : ι → Submodule ℝ E)
    (htrans : ∀ i, D i ⊔ A.direction = ⊤)
    (hinter : ∀ i, D i ⊓ A.direction ≠ ⊥) (p : E) :
    Dense {v : A.direction | ∀ i, D i ⊔ (childCut A p (v : E)).direction = ⊤} := by
  simpa only [childCut_direction] using
    dense_normals_preserving_transversality A.direction D htrans hinter

end Affine

end Erdos909.GenericCut
