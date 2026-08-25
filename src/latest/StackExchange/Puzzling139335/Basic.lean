import StackExchange.Puzzling139335.Definitions
import Mathlib.Analysis.Normed.Affine.MazurUlam

/-!
# Congruences and the protected center

The dissection uses full Euclidean congruences. Mazur--Ulam identifies
the affine-isometry formulation with arbitrary isometry equivalences of
the plane. The fixed-point obstruction below is used only when an actual
congruence between two pieces is known to fix the square center.
-/

open Set

namespace Puzzling139335

namespace Congruent

theorem refl (P : Set Plane) : Congruent P P := by
  refine ⟨AffineIsometryEquiv.refl ℝ Plane, ?_⟩
  exact Set.image_id _

theorem symm {P Q : Set Plane} (h : Congruent P Q) : Congruent Q P := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, ?_⟩
  rw [← he, Set.image_image]
  simp

theorem trans {P Q R : Set Plane} (hPQ : Congruent P Q)
    (hQR : Congruent Q R) : Congruent P R := by
  obtain ⟨e, he⟩ := hPQ
  obtain ⟨f, hf⟩ := hQR
  refine ⟨e.trans f, ?_⟩
  rw [← hf, ← he, Set.image_image]
  rfl

end Congruent

/-- There is no orientation or linearity restriction hidden in `Congruent`. -/
theorem congruent_iff_isometryEquiv {P Q : Set Plane} :
    Congruent P Q ↔ ∃ e : Plane ≃ᵢ Plane, e '' P = Q := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e.toIsometryEquiv, he⟩
  · rintro ⟨e, he⟩
    exact ⟨e.toRealAffineIsometryEquiv, he⟩

theorem interior_image_affineIsometry (e : Plane ≃ᵃⁱ[ℝ] Plane) (P : Set Plane) :
    interior (e '' P) = e '' interior P :=
  (e.toHomeomorph.image_interior P).symm

theorem mem_interior_image_affineIsometry (e : Plane ≃ᵃⁱ[ℝ] Plane)
    {P : Set Plane} {p : Plane} :
    e p ∈ interior (e '' P) ↔ p ∈ interior P := by
  rw [interior_image_affineIsometry]
  constructor
  · rintro ⟨q, hq, heq⟩
    exact e.injective heq ▸ hq
  · intro hp
    exact mem_image_of_mem e hp

/-- A point fixed by a congruence between disjoint-interior pieces cannot
be interior to either piece. No symmetry of the rest of the tiling is assumed. -/
theorem not_mem_interior_of_fixed_congruence {P Q : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P = Q)
    (hdis : Disjoint (interior P) (interior Q)) {p : Plane} (hp : e p = p) :
    p ∉ interior P ∧ p ∉ interior Q := by
  have hmem : p ∈ interior P ↔ p ∈ interior Q := by
    simpa only [he, hp] using
      (mem_interior_image_affineIsometry e (P := P) (p := p)).symm
  constructor
  · intro hP
    exact Set.disjoint_left.mp hdis hP (hmem.mp hP)
  · intro hQ
    exact Set.disjoint_left.mp hdis (hmem.mpr hQ) hQ

theorem SquareDissection.center_not_mem_fixed_pair (d : SquareDissection)
    {i j : Fin 4} (hij : i ≠ j) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece i = d.piece j) (hfix : e squareCenter = squareCenter) :
    squareCenter ∉ interior (d.piece i) ∧ squareCenter ∉ interior (d.piece j) :=
  not_mem_interior_of_fixed_congruence e he (d.disjoint_interiors hij) hfix

theorem SquareDissection.protectedCenter_unique (d : SquareDissection)
    {i j : Fin 4} (hi : squareCenter ∈ interior (d.piece i))
    (hj : squareCenter ∈ interior (d.piece j)) : i = j := by
  by_contra hij
  exact Set.disjoint_left.mp (d.disjoint_interiors hij) hi hj

/-- Relabeling pieces changes no geometric hypothesis. -/
def SquareDissection.reindex (d : SquareDissection) (σ : Equiv.Perm (Fin 4)) :
    SquareDissection where
  piece i := d.piece (σ i)
  jordan i := d.jordan (σ i)
  congruent i j := d.congruent (σ i) (σ j)
  covers := by
    ext p
    constructor
    · intro hp
      obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      exact d.piece_subset (σ i) hi
    · intro hp
      obtain ⟨i, hi⟩ := d.exists_piece_mem hp
      exact mem_iUnion.mpr ⟨σ.symm i, by simpa using hi⟩
  disjoint_interiors := by
    intro i j hij
    exact d.disjoint_interiors (fun heq => hij (σ.injective heq))

@[simp] theorem SquareDissection.reindex_hasProtectedCenter
    (d : SquareDissection) (σ : Equiv.Perm (Fin 4)) :
    (d.reindex σ).HasProtectedCenter ↔ d.HasProtectedCenter := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨σ i, hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨σ.symm i, ?_⟩
    simpa only [reindex, σ.apply_symm_apply] using hi

end Puzzling139335
