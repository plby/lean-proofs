/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.CoordinateFlag
import ErdosProblems.Erdos186.CFP.Bilu.Proposition75Case2Construction

/-!
# Bilu Section 9.3: standard coordinates on a rational section

For a proper rational subspace whose literal integral points span it, this
file chooses a basis of the full intersection lattice and promotes that
integral basis to a real basis.  Thus a seminorm restricted to the subspace
can be pulled back to a literal standard lattice without adding a lattice
index to the volume estimate.
-/

namespace Erdos186.CFP.Bilu.Section93LatticeSectionCoordinates

open Set Module Submodule MeasureTheory
open Mahler SubspaceLattice
open Proposition75Case2Construction

noncomputable section

set_option autoImplicit false

variable {n : ℕ}

/-- A full basis of `L ∩ ℤⁿ`, indexed by the real dimension of `L`. -/
theorem nonempty_integralBasis
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hproper : L ≠ ⊤)
    (hspan : Submodule.span ℝ
      ((integralPoints L : Submodule ℤ L) : Set L) = ⊤) :
    Nonempty (Basis (Fin (finrank ℝ L)) ℤ (integralPoints L)) := by
  classical
  obtain ⟨s, P, hSat⟩ := exists_saturatedPresentation L hproper hspan
  letI hdiscRow : DiscreteTopology P.rowLattice := by
    change DiscreteTopology (Submodule.span ℤ (Set.range P.rowBasis))
    infer_instance
  letI : DiscreteTopology (integralPoints L) := hSat ▸ hdiscRow
  letI : IsZLattice ℝ (integralPoints L) := ⟨hspan⟩
  letI : Module.Free ℤ (integralPoints L) := ZLattice.module_free ℝ _
  letI : Module.Finite ℤ (integralPoints L) := ZLattice.module_finite ℝ _
  exact ⟨(Module.Free.chooseBasis ℤ (integralPoints L)).reindex
    (Fintype.equivOfCardEq (by
      rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ,
        Fintype.card_fin]))⟩

/-- The chosen full intersection-lattice basis. -/
noncomputable def integralBasis
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hproper : L ≠ ⊤)
    (hspan : Submodule.span ℝ
      ((integralPoints L : Submodule ℤ L) : Set L) = ⊤) :
    Basis (Fin (finrank ℝ L)) ℤ (integralPoints L) :=
  Classical.choice (nonempty_integralBasis L hproper hspan)

/-- The same lattice basis promoted to a real basis of the section. -/
noncomputable def realBasis
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hproper : L ≠ ⊤)
    (hspan : Submodule.span ℝ
      ((integralPoints L : Submodule ℤ L) : Set L) = ⊤) :
    Basis (Fin (finrank ℝ L)) ℝ L := by
  classical
  letI : DiscreteTopology (integralPoints L) := by
    obtain ⟨s, P, hSat⟩ := exists_saturatedPresentation L hproper hspan
    letI hdiscRow : DiscreteTopology P.rowLattice := by
      change DiscreteTopology (Submodule.span ℤ (Set.range P.rowBasis))
      infer_instance
    exact hSat ▸ hdiscRow
  letI : IsZLattice ℝ (integralPoints L) := ⟨hspan⟩
  exact (integralBasis L hproper hspan).ofZLatticeBasis ℝ
    (integralPoints L)

@[simp] theorem realBasis_apply
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hproper : L ≠ ⊤)
    (hspan : Submodule.span ℝ
      ((integralPoints L : Submodule ℤ L) : Set L) = ⊤)
    (i : Fin (finrank ℝ L)) :
    realBasis L hproper hspan i = integralBasis L hproper hspan i := by
  classical
  letI : DiscreteTopology (integralPoints L) := by
    obtain ⟨s, P, hSat⟩ := exists_saturatedPresentation L hproper hspan
    letI hdiscRow : DiscreteTopology P.rowLattice := by
      change DiscreteTopology (Submodule.span ℤ (Set.range P.rowBasis))
      infer_instance
    exact hSat ▸ hdiscRow
  letI : IsZLattice ℝ (integralPoints L) := ⟨hspan⟩
  exact (integralBasis L hproper hspan).ofZLatticeBasis_apply ℝ
    (integralPoints L) i

/-- Lattice-basis coordinates, as an ambient real-linear embedding. -/
noncomputable def coordinateEmbedding
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hproper : L ≠ ⊤)
    (hspan : Submodule.span ℝ
      ((integralPoints L : Submodule ℤ L) : Set L) = ⊤) :
    (Fin (finrank ℝ L) → ℝ) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin n) :=
  L.subtype.comp (realBasis L hproper hspan).equivFun.symm.toLinearMap

/-- The same full lattice coordinates on literal integral points.  The
output is an ambient standard integral vector, not merely an existential
integrality witness in the subtype. -/
noncomputable def coordinateIntegralEmbedding
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hproper : L ≠ ⊤)
    (hspan : Submodule.span ℝ
      ((integralPoints L : Submodule ℤ L) : Set L) = ⊤) :
    (Fin (finrank ℝ L) → ℤ) →ₗ[ℤ] (Fin n → ℤ) :=
  (integralCoordinateLattice L).subtype.comp <|
    (integralCoordinateEquiv L).symm.toLinearMap.comp <|
      (integralBasis L hproper hspan).equivFun.symm.toLinearMap

/-- Realization of the integral coordinate embedding agrees with the real
coordinate embedding. -/
theorem integralReal_coordinateIntegralEmbedding
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hproper : L ≠ ⊤)
    (hspan : Submodule.span ℝ
      ((integralPoints L : Submodule ℤ L) : Set L) = ⊤)
    (z : Fin (finrank ℝ L) → ℤ) :
    integralReal (coordinateIntegralEmbedding L hproper hspan z) =
      coordinateEmbedding L hproper hspan (integralEmbed z) := by
  classical
  letI : DiscreteTopology (integralPoints L) := by
    obtain ⟨s, P, hSat⟩ := exists_saturatedPresentation L hproper hspan
    letI hdiscRow : DiscreteTopology P.rowLattice := by
      change DiscreteTopology (Submodule.span ℤ (Set.range P.rowBasis))
      infer_instance
    exact hSat ▸ hdiscRow
  letI : IsZLattice ℝ (integralPoints L) := ⟨hspan⟩
  let q : integralPoints L :=
    (integralBasis L hproper hspan).equivFun.symm z
  have hqambient :
      integralReal (coordinateIntegralEmbedding L hproper hspan z) =
        ((q : L) : EuclideanSpace ℝ (Fin n)) := by
    change integralReal
      (((integralCoordinateEquiv L).symm
        ((integralBasis L hproper hspan).equivFun.symm z) :
          integralCoordinateLattice L) : Fin n → ℤ) = _
    exact (integralCoordinateEquiv_coe L
      ((integralCoordinateEquiv L).symm q)).symm.trans <| by
        rw [(integralCoordinateEquiv L).apply_symm_apply]
  rw [hqambient]
  apply congrArg (fun x : L ↦ (x : EuclideanSpace ℝ (Fin n)))
  change (q : L) =
    (realBasis L hproper hspan).equivFun.symm (integralEmbed z)
  apply (realBasis L hproper hspan).equivFun.injective
  rw [(realBasis L hproper hspan).equivFun.apply_symm_apply]
  ext i
  rw [show ((realBasis L hproper hspan).equivFun q) i =
      (((integralBasis L hproper hspan).equivFun q) i : ℝ) by
    exact (integralBasis L hproper hspan).ofZLatticeBasis_repr_apply
      ℝ (integralPoints L) q i]
  simp [q, integralEmbed]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [Finsupp.single_apply, hji]
  · simp

/-- Pull a seminorm on the ambient space back through the full section
lattice coordinates. -/
noncomputable def coordinateSeminorm
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hproper : L ≠ ⊤)
    (hspan : Submodule.span ℝ
      ((integralPoints L : Submodule ℤ L) : Set L) = ⊤)
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin n))) :
    Seminorm ℝ (Fin (finrank ℝ L) → ℝ) :=
  p.comp (coordinateEmbedding L hproper hspan)

theorem coordinateSeminorm_definite
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hproper : L ≠ ⊤)
    (hspan : Submodule.span ℝ
      ((integralPoints L : Submodule ℤ L) : Set L) = ⊤)
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (hp : ∀ x, p x = 0 → x = 0) :
    Mahler.IsDefinite (coordinateSeminorm L hproper hspan p) := by
  intro x hx
  have hamb :
      (((realBasis L hproper hspan).equivFun.symm x : L) :
        EuclideanSpace ℝ (Fin n)) = 0 := hp _ hx
  have hsub : (realBasis L hproper hspan).equivFun.symm x = 0 :=
    Subtype.ext hamb
  exact (realBasis L hproper hspan).equivFun.symm.injective <| by
    simpa using hsub

end

end Erdos186.CFP.Bilu.Section93LatticeSectionCoordinates

#print axioms
  Erdos186.CFP.Bilu.Section93LatticeSectionCoordinates.coordinateSeminorm_definite
