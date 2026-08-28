import Wikipedia.HopfProblem.OrbitPairHomotopyExtensionCylinder
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Neighborhood deformation data from a closed homotopy-extension inclusion

The cylinder retraction supplies a spatial deformation. The supremum
norm of its time-coordinate defect is a continuous function to `[0,1]`.
Its zero set is exactly the included closed subspace, and its strict
sublevel at one is carried into that subspace by the final deformation.
-/

noncomputable section

universe u

open CategoryTheory unitInterval Set Filter Topology

namespace Wikipedia.HopfProblem.OrbitPair.NeighborhoodDeformation

open HomotopyExtension

structure Data {A B : TopCat.{u}} (i : A ⟶ B) where
  height : C(B, I)
  deformation : C(I × B, B)
  zero_iff : ∀ b, height b = 0 ↔ b ∈ Set.range i
  bottom : ∀ b, deformation (0, b) = b
  fixed : ∀ t a, deformation (t, i a) = i a
  terminal : ∀ b, height b < 1 → deformation (1, b) ∈ Set.range i

variable {A B : TopCat.{u}} {i : A ⟶ B} (R : C(I × B, ↥(cylinderBase i)))

def timeDefect : C(I × B, ℝ) where
  toFun p := (p.1 : ℝ) - ((R p).val.1 : ℝ)
  continuous_toFun := (continuous_subtype_val.comp continuous_fst).sub
    (continuous_subtype_val.comp (continuous_fst.comp
      (continuous_subtype_val.comp R.continuous)))

def timeDefectPaths : C(B, C(I, ℝ)) :=
  ((timeDefect R).comp ⟨Prod.swap, continuous_swap⟩).curry

theorem timeDefectPaths_apply (b : B) (t : I) :
    timeDefectPaths R b t = (t : ℝ) - ((R (t, b)).val.1 : ℝ) := rfl

theorem timeDefect_norm_le (b : B) : ‖timeDefectPaths R b‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ zero_le_one).mpr
  intro t
  rw [timeDefectPaths_apply, Real.norm_eq_abs, abs_le]
  have ht0 := t.property.1
  have ht1 := t.property.2
  have hr0 := (R (t, b)).val.1.property.1
  have hr1 := (R (t, b)).val.1.property.2
  constructor <;> linarith

def height : C(B, I) where
  toFun b := ⟨‖timeDefectPaths R b‖, norm_nonneg _, timeDefect_norm_le R b⟩
  continuous_toFun := (timeDefectPaths R).continuous.norm.subtype_mk _

theorem height_zero_time (b : B) (hb : height R b = 0) (t : I) :
    (R (t, b)).val.1 = t := by
  have hn : ‖timeDefectPaths R b‖ = 0 := congrArg Subtype.val hb
  have hz : timeDefectPaths R b = 0 := norm_eq_zero.mp hn
  have ht : (t : ℝ) - ((R (t, b)).val.1 : ℝ) = 0 := ContinuousMap.congr_fun hz t
  exact Subtype.ext (sub_eq_zero.mp ht).symm

theorem height_image_zero
    (hRi : ∀ t a, R (t, i a) = cylinderSide i (t, a)) (a : A) : height R (i a) = 0 := by
  have hz : timeDefectPaths R (i a) = 0 := by
    apply ContinuousMap.ext
    intro t
    change (t : ℝ) - ((R (t, i a)).val.1 : ℝ) = 0
    rw [hRi]
    exact sub_self _
  apply Subtype.ext
  change ‖timeDefectPaths R (i a)‖ = 0
  rw [hz, norm_zero]

theorem height_zero_iff (hc : IsClosedEmbedding i)
    (hR0 : ∀ b, R (0, b) = cylinderBottom i b)
    (hRi : ∀ t a, R (t, i a) = cylinderSide i (t, a)) (b : B) :
    height R b = 0 ↔ b ∈ Set.range i := by
  constructor
  · intro hb
    let γ : ℝ → B := fun t ↦ (R (Set.projIcc 0 1 zero_le_one t, b)).val.2
    have hγ : Continuous γ := continuous_snd.comp
      (continuous_subtype_val.comp (R.continuous.comp
        (continuous_projIcc.prodMk continuous_const)))
    have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∈ Set.range i := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      change (0 : ℝ) < t at ht
      have hn : Set.projIcc 0 1 zero_le_one t ≠ (0 : I) := by
        intro he
        exact (not_le_of_gt ht) (_root_.projIcc_eq_zero.mp he)
      rcases (R (Set.projIcc 0 1 zero_le_one t, b)).property with hz | hs
      · exact False.elim (hn ((height_zero_time R b hb _).symm.trans hz))
      · exact hs
    have hlim : γ 0 ∈ Set.range i := hc.isClosed_range.mem_of_tendsto
      ((hγ.tendsto 0).mono_left nhdsWithin_le_nhds) hmem
    have hγ0 : γ 0 = b := by
      change (R (Set.projIcc 0 1 zero_le_one 0, b)).val.2 = b
      rw [Set.projIcc_left]
      change (R (0, b)).val.2 = b
      rw [hR0]
      rfl
    exact hγ0 ▸ hlim
  · rintro ⟨a, rfl⟩
    exact height_image_zero R hRi a

theorem height_lt_one_terminal (b : B) (hb : height R b < 1) :
    (R (1, b)).val.2 ∈ Set.range i := by
  rcases (R (1, b)).property with hz | hs
  · have hn : ‖timeDefectPaths R b‖ < 1 := hb
    have ht := ((timeDefectPaths R b).norm_lt_iff zero_lt_one).mp hn (1 : I)
    rw [timeDefectPaths_apply, hz] at ht
    norm_num at ht
  · exact hs

def ofCylinderRetraction (hc : IsClosedEmbedding i)
    (hR0 : ∀ b, R (0, b) = cylinderBottom i b)
    (hRi : ∀ t a, R (t, i a) = cylinderSide i (t, a)) : Data i where
  height := height R
  deformation := ⟨fun p ↦ (R p).val.2,
    continuous_snd.comp (continuous_subtype_val.comp R.continuous)⟩
  zero_iff := height_zero_iff R hc hR0 hRi
  bottom b := congrArg (fun p : ↥(cylinderBase i) ↦ p.val.2) (hR0 b)
  fixed t a := congrArg (fun p : ↥(cylinderBase i) ↦ p.val.2) (hRi t a)
  terminal := height_lt_one_terminal R

theorem exists_data (i : A ⟶ B) (hi : HasHomotopyExtension i) (hc : IsClosedEmbedding i) :
    Nonempty (Data i) := by
  obtain ⟨R, hR0, hRi⟩ := exists_cylinder_retraction i hi
  exact ⟨ofCylinderRetraction R hc hR0 hRi⟩

end Wikipedia.HopfProblem.OrbitPair.NeighborhoodDeformation
