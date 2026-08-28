import Wikipedia.HopfProblem.OrbitPairNeighborhoodDeformationControl

/-!
# A cylinder retraction from neighborhood deformation data

The time coordinate is the positive part of `t - height(x)`. The
spatial coordinate runs the given deformation at the clipped time
`t / height(x)`. At height zero, arbitrary time changes are continuous
because the deformation fixes that subspace uniformly in time.
-/

noncomputable section

universe u

open CategoryTheory unitInterval Set Topology

namespace Wikipedia.HopfProblem.OrbitPair.NeighborhoodDeformation

open HomotopyExtension

variable {A B : TopCat.{u}} {i : A ⟶ B} (D : Data i)

def retractionTime : C(I × B, I) :=
  ⟨fun p ↦ Set.projIcc 0 1 zero_le_one ((p.1 : ℝ) - (D.height p.2 : ℝ)),
    continuous_projIcc.comp ((continuous_subtype_val.comp continuous_fst).sub
      (continuous_subtype_val.comp (D.height.continuous.comp continuous_snd)))⟩

def deformationTime (p : I × B) : I :=
  Set.projIcc 0 1 zero_le_one ((p.1 : ℝ) / (D.height p.2 : ℝ))

def retractionPoint : C(I × B, B) where
  toFun p := D.deformation (deformationTime D p, p.2)
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro p
    by_cases hp : D.height p.2 = 0
    · exact continuousAt_retime_at_zero D Prod.snd (deformationTime D) p
        continuous_snd.continuousAt hp
    · have hn : (D.height p.2 : ℝ) ≠ 0 := fun h ↦ hp (Subtype.ext h)
      have ht : ContinuousAt (deformationTime D) p := continuous_projIcc.continuousAt.comp
        ((continuous_subtype_val.comp continuous_fst).continuousAt.div
          (continuous_subtype_val.comp (D.height.continuous.comp continuous_snd)).continuousAt hn)
      exact D.deformation.continuous.continuousAt.comp (ht.prodMk continuous_snd.continuousAt)

theorem retraction_mem (p : I × B) :
    (retractionTime D p, retractionPoint D p) ∈ cylinderBase i := by
  by_cases hu : D.height p.2 = 0
  · right
    change D.deformation (deformationTime D p, p.2) ∈ Set.range i
    rw [fixed_of_height_zero D _ _ hu]
    exact (D.zero_iff _).mp hu
  · by_cases ht : (p.1 : ℝ) ≤ (D.height p.2 : ℝ)
    · left
      exact _root_.projIcc_eq_zero.mpr (sub_nonpos.mpr ht)
    · right
      have hn : (D.height p.2 : ℝ) ≠ 0 := fun h ↦ hu (Subtype.ext h)
      have hpos : (0 : ℝ) < D.height p.2 :=
        lt_of_le_of_ne (D.height p.2).property.1 hn.symm
      have htime : deformationTime D p = 1 := by
        apply _root_.projIcc_eq_one.mpr
        apply (le_div_iff₀ hpos).mpr
        simpa only [one_mul] using (not_le.mp ht).le
      change D.deformation (deformationTime D p, p.2) ∈ Set.range i
      rw [htime]
      exact D.terminal p.2 (lt_of_lt_of_le (not_le.mp ht) p.1.property.2)

def cylinderRetraction : C(I × B, ↥(cylinderBase i)) where
  toFun p := ⟨(retractionTime D p, retractionPoint D p), retraction_mem D p⟩
  continuous_toFun := ((retractionTime D).continuous.prodMk
    (retractionPoint D).continuous).subtype_mk _

theorem cylinderRetraction_bottom (b : B) : cylinderRetraction D (0, b) = cylinderBottom i b := by
  apply Subtype.ext
  apply Prod.ext
  · change Set.projIcc 0 1 zero_le_one (0 - (D.height b : ℝ)) = (0 : I)
    exact _root_.projIcc_eq_zero.mpr (sub_nonpos.mpr (D.height b).property.1)
  · change D.deformation
      (Set.projIcc 0 1 zero_le_one ((0 : ℝ) / (D.height b : ℝ)), b) = b
    rw [zero_div, Set.projIcc_left]
    exact D.bottom b

theorem cylinderRetraction_side (t : I) (a : A) :
    cylinderRetraction D (t, i a) = cylinderSide i (t, a) := by
  apply Subtype.ext
  apply Prod.ext
  · change Set.projIcc 0 1 zero_le_one ((t : ℝ) - (D.height (i a) : ℝ)) = t
    rw [height_image]
    change Set.projIcc 0 1 zero_le_one ((t : ℝ) - (0 : ℝ)) = t
    rw [sub_zero]
    exact Set.projIcc_val zero_le_one t
  · exact D.fixed _ a

end Wikipedia.HopfProblem.OrbitPair.NeighborhoodDeformation
