import Wikipedia.NoExoticSixSphere.JamesSphereCharacteristic
import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# Continuous inverse charts of the actual James cells

The closed characteristic disk is a compact quotient onto its stage.
Restriction over the open exact-length stratum remains a quotient map.
The inverse furnished by interior injectivity is therefore continuous.
This supplies the actual partial equivalences needed by Mathlib's CW data.
-/

noncomputable section

open Set Metric Topology

namespace NoExoticSixSphere.JamesSphere.Cell

def inverse (n k : ℕ) (w : James.Space (Sphere n) (spherePole n)) : Fin (k * n) → ℝ := by
  classical
  exact if h : w ∈ characteristic n k '' ball 0 1 then Classical.choose h else 0

theorem inverse_mem (n k : ℕ) {w : James.Space (Sphere n) (spherePole n)}
    (hw : w ∈ characteristic n k '' ball 0 1) : inverse n k w ∈ ball 0 1 := by
  classical
  rw [inverse, dif_pos hw]
  exact (Classical.choose_spec hw).1

theorem characteristic_inverse (n k : ℕ) {w : James.Space (Sphere n) (spherePole n)}
    (hw : w ∈ characteristic n k '' ball 0 1) : characteristic n k (inverse n k w) = w := by
  classical
  rw [inverse, dif_pos hw]
  exact (Classical.choose_spec hw).2

theorem inverse_characteristic (n k : ℕ) {x : Fin (k * n) → ℝ} (hx : x ∈ ball 0 1) :
    inverse n k (characteristic n k x) = x := by
  have hm : characteristic n k x ∈ characteristic n k '' ball 0 1 := ⟨x, hx, rfl⟩
  exact injOn_ball n k (inverse_mem n k hm) hx (characteristic_inverse n k hm)

def chart (n k : ℕ) : PartialEquiv (Fin (k * n) → ℝ)
    (James.Space (Sphere n) (spherePole n)) where
  toFun := characteristic n k
  invFun := inverse n k
  source := ball 0 1
  target := characteristic n k '' ball 0 1
  map_source' x hx := ⟨x, hx, rfl⟩
  map_target' _ hw := inverse_mem n k hw
  left_inv' _ hx := inverse_characteristic n k hx
  right_inv' _ hw := characteristic_inverse n k hw

theorem chart_source (n k : ℕ) : (chart n k).source = ball 0 1 := rfl

theorem chart_continuousOn (n k : ℕ) : ContinuousOn (chart n k) (closedBall 0 1) :=
  (characteristic n k).continuous.continuousOn

def closedPresentation (n k : ℕ) :
    C((closedBall 0 1 : Set (Fin (k * n) → ℝ)), James.stage (spherePole n) k) :=
  ⟨fun x ↦ ⟨characteristic n k x.val, characteristic_mem_stage n k x.val⟩,
    ((characteristic n k).continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem closedPresentation_surjective (n k : ℕ) (hn : 0 < n) :
    Function.Surjective (closedPresentation n k) := by
  intro w
  have hw : w.val ∈ characteristic n k '' closedBall 0 1 :=
    (Set.ext_iff.mp (image_closedBall n k hn) w.val).mpr w.property
  obtain ⟨x, hx, he⟩ := hw
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

theorem isQuotientMap_closedPresentation (n k : ℕ) (hn : 0 < n) :
    IsQuotientMap (closedPresentation n k) :=
  IsQuotientMap.of_surjective_continuous (closedPresentation_surjective n k hn)
    (closedPresentation n k).continuous

def topStratum (n k : ℕ) : Set (James.stage (spherePole n) k) :=
  {w | James.size (spherePole n) w.val = k}

theorem preimage_topStratum (n k : ℕ) :
    closedPresentation n k ⁻¹' topStratum n k = {x | x.val ∈ ball 0 1} := by
  ext x
  exact size_characteristic_eq_iff n k x.val

theorem isOpen_topStratum (n k : ℕ) (hn : 0 < n) : IsOpen (topStratum n k) := by
  apply (isQuotientMap_closedPresentation n k hn).isOpen_preimage.mp
  rw [preimage_topStratum]
  exact isOpen_ball.preimage continuous_subtype_val

theorem continuous_inverse_topStratum (n k : ℕ) (hn : 0 < n) :
    Continuous (fun w : topStratum n k ↦ inverse n k w.val.val) := by
  have hq := (isQuotientMap_closedPresentation n k hn).restrictPreimage_isOpen
    (isOpen_topStratum n k hn)
  apply hq.continuous_iff.mpr
  have he : (fun x : closedPresentation n k ⁻¹' topStratum n k ↦
      inverse n k (closedPresentation n k x.val).val) = (fun x ↦ x.val.val) := by
    funext x
    apply inverse_characteristic n k
    exact (size_characteristic_eq_iff n k x.val.val).mp x.property
  change Continuous (fun x : closedPresentation n k ⁻¹' topStratum n k ↦
    inverse n k (closedPresentation n k x.val).val)
  rw [he]
  exact continuous_subtype_val.comp continuous_subtype_val

theorem chart_continuousOn_symm (n k : ℕ) (hn : 0 < n) :
    ContinuousOn (chart n k).symm (chart n k).target := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hsize (w : characteristic n k '' ball 0 1) : James.size (spherePole n) w.val = k :=
    (Set.ext_iff.mp (image_ball n k hn) w.val).mp w.property
  let f : (characteristic n k '' ball 0 1) → topStratum n k := fun w ↦
    ⟨⟨w.val, le_of_eq (hsize w)⟩, hsize w⟩
  have hf : Continuous f := (continuous_subtype_val.subtype_mk _).subtype_mk _
  exact (continuous_inverse_topStratum n k hn).comp hf

end NoExoticSixSphere.JamesSphere.Cell
