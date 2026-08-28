import Wikipedia.HopfProblem.OrbitPairNeighborhoodProductTime

/-!
# Jointly continuous motion for the product-boundary union

The ratio functions need not be continuous where both heights vanish.
The checked uniform stationarity theorem proves continuity of the
resulting deformations there, without requiring continuity of those
time functions themselves.
-/

noncomputable section

universe u v

open CategoryTheory unitInterval Set Topology

namespace Wikipedia.HopfProblem.OrbitPair.NeighborhoodProduct

open NeighborhoodDeformation

variable {A X : TopCat.{u}} {B Y : TopCat.{v}} {i : A ⟶ X} {j : B ⟶ Y}
    (D : Data i) (E : Data j)

def boundary (i : A ⟶ X) (j : B ⟶ Y) : Set (X × Y) :=
  {p | p.1 ∈ Set.range i ∨ p.2 ∈ Set.range j}

def inclusion (i : A ⟶ X) (j : B ⟶ Y) :
    TopCat.of ↥(boundary i j) ⟶ TopCat.of (X × Y) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

theorem range_inclusion (i : A ⟶ X) (j : B ⟶ Y) :
    Set.range (inclusion i j) = boundary i j := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact q.property
  · intro hp
    exact ⟨⟨p, hp⟩, rfl⟩

def height : C(X × Y, I) :=
  ⟨fun p ↦ D.height p.1 * E.height p.2,
    (D.height.continuous.comp continuous_fst).mul (E.height.continuous.comp continuous_snd)⟩

def leftTime (p : I × (X × Y)) : I :=
  p.1 * ratio (D.height p.2.1) (E.height p.2.2)

def leftMotion : C(I × (X × Y), X) where
  toFun p := D.deformation (leftTime D E p, p.2.1)
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro p
    by_cases hp : D.height p.2.1 = 0
    · exact continuousAt_retime_at_zero D (fun q : I × (X × Y) ↦ q.2.1)
        (leftTime D E) p continuous_snd.fst.continuousAt hp
    · have hr : ContinuousAt
          (fun q : I × (X × Y) ↦ ratio (D.height q.2.1) (E.height q.2.2)) p :=
        (ratio_continuousAt (D.height p.2.1, E.height p.2.2) hp).comp
          (f := fun q : I × (X × Y) ↦ (D.height q.2.1, E.height q.2.2))
          (((D.height.continuous.comp continuous_snd.fst).prodMk
            (E.height.continuous.comp continuous_snd.snd)).continuousAt)
      have ht : ContinuousAt (leftTime D E) p := continuous_fst.continuousAt.mul hr
      exact D.deformation.continuous.continuousAt.comp (ht.prodMk continuous_snd.fst.continuousAt)

def rightMotion : C(I × (X × Y), Y) :=
  (leftMotion E D).comp
    ⟨fun p ↦ (p.1, (p.2.2, p.2.1)),
      continuous_fst.prodMk (continuous_snd.snd.prodMk continuous_snd.fst)⟩

def deformation : C(I × (X × Y), X × Y) := (leftMotion D E).prodMk (rightMotion D E)

theorem deformation_apply (t : I) (x : X) (y : Y) :
    deformation D E (t, (x, y)) =
      (D.deformation (t * ratio (D.height x) (E.height y), x),
        E.deformation (t * ratio (E.height y) (D.height x), y)) := rfl

theorem deformation_bottom (p : X × Y) : deformation D E (0, p) = p := by
  rcases p with ⟨x, y⟩
  rw [deformation_apply, zero_mul, zero_mul, D.bottom, E.bottom]

theorem deformation_fixed_left (t : I) (x : X) (y : Y) (hx : D.height x = 0) :
    deformation D E (t, (x, y)) = (x, y) := by
  apply Prod.ext
  · exact fixed_of_height_zero D _ x hx
  · change E.deformation (t * ratio (E.height y) (D.height x), y) = y
    rw [hx, ratio_right_zero, mul_zero]
    exact E.bottom y

theorem deformation_fixed_right (t : I) (x : X) (y : Y) (hy : E.height y = 0) :
    deformation D E (t, (x, y)) = (x, y) := by
  apply Prod.ext
  · change D.deformation (t * ratio (D.height x) (E.height y), x) = x
    rw [hy, ratio_right_zero, mul_zero]
    exact D.bottom x
  · exact fixed_of_height_zero E _ y hy

theorem deformation_fixed (t : I) (p : X × Y) (hp : p ∈ boundary i j) :
    deformation D E (t, p) = p := by
  rcases hp with hx | hy
  · exact deformation_fixed_left D E t p.1 p.2 ((D.zero_iff _).mpr hx)
  · exact deformation_fixed_right D E t p.1 p.2 ((E.zero_iff _).mpr hy)

end Wikipedia.HopfProblem.OrbitPair.NeighborhoodProduct
