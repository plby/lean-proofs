import StackExchange.Puzzling139335.RectangularHull.Interlacing.Regions

/-!
# Packing the orbit of two commuting involutions

For the four-element orbit, the three given disjointness relations generate
the other three by transporting interiors through the affine isometries.
-/

open Set

namespace Puzzling139335.SymmetryOrbit

noncomputable section

/-- The four actual affine-isometric placements of the orbit. -/
def commutingPlacements (e f : Plane ≃ᵃⁱ[ℝ] Plane) : Fin 4 → Plane ≃ᵃⁱ[ℝ] Plane :=
  ![AffineIsometryEquiv.refl ℝ Plane, e, f, e.trans f]

/-- The orbit ordered as the identity, the first generator, the second generator,
and their product. -/
def commutingOrbit (e f : Plane ≃ᵃⁱ[ℝ] Plane) (P : Set Plane) : Fin 4 → Set Plane :=
  ![P, e '' P, f '' P, (e.trans f) '' P]

@[simp] theorem commutingOrbit_zero (e f : Plane ≃ᵃⁱ[ℝ] Plane) (P : Set Plane) :
    commutingOrbit e f P 0 = P := rfl

@[simp] theorem commutingOrbit_one (e f : Plane ≃ᵃⁱ[ℝ] Plane) (P : Set Plane) :
    commutingOrbit e f P 1 = e '' P := rfl

@[simp] theorem commutingOrbit_two (e f : Plane ≃ᵃⁱ[ℝ] Plane) (P : Set Plane) :
    commutingOrbit e f P 2 = f '' P := rfl

@[simp] theorem commutingOrbit_three (e f : Plane ≃ᵃⁱ[ℝ] Plane) (P : Set Plane) :
    commutingOrbit e f P 3 = (e.trans f) '' P := rfl

/-- The set family is realized by the corresponding actual placements. -/
@[simp] theorem commutingPlacements_image (e f : Plane ≃ᵃⁱ[ℝ] Plane)
    (P : Set Plane) (i : Fin 4) :
    commutingPlacements e f i '' P = commutingOrbit e f P i := by
  fin_cases i <;> simp [commutingPlacements, commutingOrbit]

/-- Three pairwise disjoint orbit interiors force all four orbit interiors to
be pairwise disjoint. No topological assumption on the original set is needed. -/
theorem pairwise_disjoint_commutingOrbit {e f : Plane ≃ᵃⁱ[ℝ] Plane} {P : Set Plane}
    (he : Function.Involutive e) (hf : Function.Involutive f)
    (hcomm : Function.Commute e f)
    (hPe : Disjoint (interior P) (interior (e '' P)))
    (hPf : Disjoint (interior P) (interior (f '' P)))
    (hef : Disjoint (interior (e '' P)) (interior (f '' P))) :
    Pairwise fun i j => Disjoint (interior (commutingOrbit e f P i))
      (interior (commutingOrbit e f P j)) := by
  have hff : f '' (f '' P) = P := by
    rw [image_image]
    change ((f : Plane → Plane) ∘ f) '' P = P
    rw [hf.comp_self, image_id]
  have hfe : f '' (e '' P) = (e.trans f) '' P := by
    rw [image_image, AffineIsometryEquiv.coe_trans]
    rfl
  have hefImage : e '' (f '' P) = (e.trans f) '' P := by
    rw [image_image, AffineIsometryEquiv.coe_trans]
    congr 1
    exact funext hcomm
  have hproductE : (e.trans f) '' (e '' P) = f '' P := by
    rw [image_image]
    congr 1
    funext x
    change f (e (e x)) = f x
    rw [he x]
  have h03 : Disjoint (interior P) (interior ((e.trans f) '' P)) := by
    have h := RectangularHull.disjoint_interiors_image_homeomorph hef f.toHomeomorph
    change Disjoint (interior (f '' (e '' P))) (interior (f '' (f '' P))) at h
    rw [hfe, hff] at h
    exact h.symm
  have h13 : Disjoint (interior (e '' P)) (interior ((e.trans f) '' P)) := by
    have h := RectangularHull.disjoint_interiors_image_homeomorph hPf e.toHomeomorph
    change Disjoint (interior (e '' P)) (interior (e '' (f '' P))) at h
    rwa [hefImage] at h
  have h23 : Disjoint (interior (f '' P)) (interior ((e.trans f) '' P)) := by
    have h := RectangularHull.disjoint_interiors_image_homeomorph hPe
      (e.trans f).toHomeomorph
    change Disjoint (interior ((e.trans f) '' P))
      (interior ((e.trans f) '' (e '' P))) at h
    rw [hproductE] at h
    exact h.symm
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
    | exact (hij rfl).elim
    | exact hPe
    | exact hPf
    | exact hef
    | exact h03
    | exact h13
    | exact h23
    | exact hPe.symm
    | exact hPf.symm
    | exact hef.symm
    | exact h03.symm
    | exact h13.symm
    | exact h23.symm

/-- Every member of the orbit of a Jordan region is a Jordan region. -/
theorem commutingOrbit_jordan {e f : Plane ≃ᵃⁱ[ℝ] Plane} {P : Set Plane}
    (hP : IsJordanRegion P) (i : Fin 4) : IsJordanRegion (commutingOrbit e f P i) := by
  fin_cases i
  · exact hP
  · exact hP.image_homeomorph e.toHomeomorph
  · exact hP.image_homeomorph f.toHomeomorph
  · exact hP.image_homeomorph (e.trans f).toHomeomorph

/-- An ambient set preserved by both generators contains the entire orbit. -/
theorem commutingOrbit_subset {e f : Plane ≃ᵃⁱ[ℝ] Plane} {P S : Set Plane}
    (hPS : P ⊆ S) (heS : e '' S ⊆ S) (hfS : f '' S ⊆ S) (i : Fin 4) :
    commutingOrbit e f P i ⊆ S := by
  fin_cases i
  · exact hPS
  · exact (image_mono hPS).trans heS
  · exact (image_mono hPS).trans hfS
  · change (e.trans f) '' P ⊆ S
    rw [AffineIsometryEquiv.coe_trans, image_comp]
    exact (image_mono ((image_mono hPS).trans heS)).trans hfS

end

end Puzzling139335.SymmetryOrbit
