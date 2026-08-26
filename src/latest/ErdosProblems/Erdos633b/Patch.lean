import ErdosProblems.Erdos633b.Geometry
import Mathlib.Data.Fintype.Sigma

/-! Finite congruent dissections of intermediate regions, with actual closed coverage. -/

namespace Erdos633b

/-- A finite family of rigid copies of one triangle covering a specified set. -/
structure Patch (R : Triangle) (S : Set Plane) (n : ℕ) where
  place : Fin n → Plane ≃ᵃⁱ[ℝ] Plane
  covers : (⋃ i, place i '' R.support) = S
  disjoint_interiors : Pairwise fun i j =>
    Disjoint (interior (place i '' R.support)) (interior (place j '' R.support))

namespace Patch

noncomputable def ofFintype {ι : Type*} [Fintype ι] (R : Triangle) (S : Set Plane)
    (place : ι → Plane ≃ᵃⁱ[ℝ] Plane) (hc : (⋃ i, place i '' R.support) = S)
    (hd : Pairwise fun i j =>
      Disjoint (interior (place i '' R.support)) (interior (place j '' R.support))) :
    Patch R S (Fintype.card ι) where
  place k := place ((Fintype.equivFin ι).symm k)
  covers := by
    rw [← hc]
    ext p
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨(Fintype.equivFin ι).symm k, hk⟩
    · rintro ⟨i, hi⟩
      exact ⟨Fintype.equivFin ι i, by simpa using hi⟩
  disjoint_interiors := fun _ _ h => hd ((Fintype.equivFin ι).symm.injective.ne h)

theorem piece_subset {R : Triangle} {S : Set Plane} {n : ℕ} (d : Patch R S n) (i : Fin n) :
    d.place i '' R.support ⊆ S := by
  intro p hp
  have h : p ∈ ⋃ j, d.place j '' R.support := Set.mem_iUnion.mpr ⟨i, hp⟩
  exact d.covers ▸ h

def toTiling {R T : Triangle} {n : ℕ} (d : Patch R T.support n) : Tiling T n where
  tile := R
  place := d.place
  covers := d.covers
  disjoint_interiors := d.disjoint_interiors

noncomputable def move {R : Triangle} {S : Set Plane} {n : ℕ} (d : Patch R S n)
    (g : Plane ≃ᵃⁱ[ℝ] Plane) : Patch R (g '' S) n where
  place i := (d.place i).trans g
  covers := by
    simp only [AffineIsometryEquiv.coe_trans, Set.image_comp, ← Set.image_iUnion, d.covers]
  disjoint_interiors := by
    intro i j hij
    simp only [AffineIsometryEquiv.coe_trans, Set.image_comp]
    have hi (s : Set Plane) : g '' interior s = interior (g '' s) :=
      g.toHomeomorph.image_interior s
    rw [← hi, ← hi]
    exact Set.disjoint_image_of_injective g.injective (d.disjoint_interiors hij)

/-- Subdivide finitely many regions with disjoint interiors and assemble the subdivisions. -/
noncomputable def glue {ι : Type*} [Fintype ι] (R : Triangle) (S : ι → Set Plane)
    (n : ι → ℕ) (d : ∀ i, Patch R (S i) (n i))
    (hd : Pairwise fun i j => Disjoint (interior (S i)) (interior (S j))) :
    Patch R (⋃ i, S i) (∑ i, n i) := by
  classical
  let f : (Σ i, Fin (n i)) → Plane ≃ᵃⁱ[ℝ] Plane := fun k => (d k.1).place k.2
  have hc : (⋃ k, f k '' R.support) = ⋃ i, S i := by
    ext p
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨⟨i, k⟩, hk⟩
      exact ⟨i, (d i).piece_subset k hk⟩
    · rintro ⟨i, hi⟩
      rw [← (d i).covers] at hi
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hi
      exact ⟨⟨i, k⟩, hk⟩
  have hp : Pairwise fun k l =>
      Disjoint (interior (f k '' R.support)) (interior (f l '' R.support)) := by
    rintro ⟨i, k⟩ ⟨j, l⟩ hkl
    by_cases hij : i = j
    · subst j
      apply (d i).disjoint_interiors
      intro h
      exact hkl (by cases h; rfl)
    · exact (hd hij).mono (interior_mono ((d i).piece_subset k))
        (interior_mono ((d j).piece_subset l))
  have result := ofFintype R (⋃ i, S i) f hc hp
  simpa only [Fintype.card_sigma, Fintype.card_fin] using result

end Patch

def Tiling.toPatch {T : Triangle} {n : ℕ} (d : Tiling T n) : Patch d.tile T.support n where
  place := d.place
  covers := d.covers
  disjoint_interiors := d.disjoint_interiors

end Erdos633b
