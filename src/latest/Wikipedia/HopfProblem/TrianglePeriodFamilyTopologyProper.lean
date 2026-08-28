import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Separation.Hausdorff

/-!
# Properness and separation from actual local product trivializations

A continuous map with compact product fibres over an open cover is proper.
The proof uses closedness local on the target and compactness of the actual
fibres, without assuming that the total space is Hausdorff.  Hausdorffness
is established separately when the base and the product fibre are Hausdorff.
-/

noncomputable section

open Set Topology TopologicalSpace

namespace Wikipedia.HopfProblem.DiagonalQuotient

variable {E B F J : Type*}
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]

/-- An actual base-compatible local product identifies each fibre over
its patch with the model fibre, without separation assumptions. -/
def fibreHomeomorphOfLocalTrivializations
    (f : E → B) (U : J → Opens B)
    (h : ∀ i, (f ⁻¹' (U i : Set B)) ≃ₜ ((U i) × F))
    (hbase : ∀ i x, ((h i x).1 : B) = f x.val)
    (i : J) (b : B) (hb : b ∈ U i) : (f ⁻¹' {b}) ≃ₜ F := by
  let lift : (f ⁻¹' {b}) → (f ⁻¹' (U i : Set B)) := fun x =>
    ⟨x.val, by
      change f x.val ∈ U i
      rw [show f x.val = b from x.property]
      exact hb⟩
  let inv : F → (f ⁻¹' {b}) := fun t =>
    ⟨((h i).symm (⟨b, hb⟩, t)).val, by
      change f ((h i).symm (⟨b, hb⟩, t)).val = b
      rw [← hbase i]
      simp⟩
  have hlift : Continuous lift := continuous_subtype_val.subtype_mk _
  have hpair (x : (f ⁻¹' {b})) :
      ((⟨b, hb⟩ : U i), (h i (lift x)).2) = h i (lift x) := by
    apply Prod.ext
    · apply Subtype.ext
      exact ((hbase i (lift x)).trans x.property).symm
    · rfl
  refine
    { toFun := fun x => (h i (lift x)).2
      invFun := inv
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := continuous_snd.comp ((h i).continuous.comp hlift)
      continuous_invFun := ?_ }
  · intro x
    apply Subtype.ext
    change ((h i).symm ((⟨b, hb⟩ : U i), (h i (lift x)).2)).val = x.val
    rw [hpair x, (h i).symm_apply_apply]
  · intro t
    change (h i (lift (inv t))).2 = t
    have hinv : lift (inv t) = (h i).symm (⟨b, hb⟩, t) := by
      apply Subtype.ext
      rfl
    rw [hinv, (h i).apply_symm_apply]
  · exact
      (continuous_subtype_val.comp
        ((h i).symm.continuous.comp (continuous_const.prodMk continuous_id))).subtype_mk _

/-- Base-compatible local product coordinates identify the full restricted
map with the product projection. -/
theorem restrictPreimage_eq_fst_comp (f : E → B) (U : J → Opens B)
    (h : ∀ i, (f ⁻¹' (U i : Set B)) ≃ₜ ((U i) × F))
    (hbase : ∀ i x, ((h i x).1 : B) = f x.val) (i : J) :
    (U i : Set B).restrictPreimage f = Prod.fst ∘ h i := by
  funext x
  apply Subtype.ext
  exact (hbase i x).symm

/-- Compact product fibres make each full base-patch restriction proper. -/
theorem restrictPreimage_proper_of_localTrivializations [CompactSpace F]
    (f : E → B) (U : J → Opens B)
    (h : ∀ i, (f ⁻¹' (U i : Set B)) ≃ₜ ((U i) × F))
    (hbase : ∀ i x, ((h i x).1 : B) = f x.val) (i : J) :
    IsProperMap ((U i : Set B).restrictPreimage f) := by
  rw [restrictPreimage_eq_fst_comp f U h hbase i]
  exact isProperMap_fst_of_compactSpace.comp (h i).isProperMap

/-- A continuous map locally trivialized with compact fibre is proper;
neither the base nor the total space is assumed Hausdorff. -/
theorem proper_of_localTrivializations [CompactSpace F]
    (f : E → B) (hf : Continuous f) (U : J → Opens B) (hU : IsOpenCover U)
    (h : ∀ i, (f ⁻¹' (U i : Set B)) ≃ₜ ((U i) × F))
    (hbase : ∀ i x, ((h i x).1 : B) = f x.val) : IsProperMap f := by
  have hp := restrictPreimage_proper_of_localTrivializations f U h hbase
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨hf, hU.isClosedMap_iff_restrictPreimage.mpr (fun i => (hp i).isClosedMap), ?_⟩
  intro b
  obtain ⟨i, hi⟩ := hU.exists_mem b
  have hc := ((hp i).isCompact_preimage
    (isCompact_singleton (x := (⟨b, hi⟩ : U i)))).image continuous_subtype_val
  simpa only [image_val_preimage_restrictPreimage, image_singleton] using hc

/-- A space locally trivialized over a Hausdorff base with Hausdorff fibre
is Hausdorff.  Equal base points lie in one common Hausdorff open patch;
distinct base points are separated by the continuous projection. -/
theorem t2Space_of_localTrivializations [T2Space B] [T2Space F]
    (f : E → B) (hf : Continuous f) (U : J → Opens B) (hU : IsOpenCover U)
    (h : ∀ i, (f ⁻¹' (U i : Set B)) ≃ₜ ((U i) × F))
    (_hbase : ∀ i x, ((h i x).1 : B) = f x.val) : T2Space E := by
  constructor
  intro x y hxy
  by_cases hb : f x = f y
  · obtain ⟨i, hi⟩ := hU.exists_mem (f x)
    have hx : x ∈ f ⁻¹' (U i : Set B) := hi
    have hy : y ∈ f ⁻¹' (U i : Set B) := by
      change f y ∈ U i
      rw [← hb]
      exact hi
    let a : f ⁻¹' (U i : Set B) := ⟨x, hx⟩
    let b : f ⁻¹' (U i : Set B) := ⟨y, hy⟩
    have hab : a ≠ b := fun he => hxy (congrArg Subtype.val he)
    let : T2Space (f ⁻¹' (U i : Set B)) := (h i).symm.t2Space
    obtain ⟨V, W, hV, hW, ha, hb', hVW⟩ := t2_separation hab
    have hopen : IsOpen (f ⁻¹' (U i : Set B)) := (U i).isOpen.preimage hf
    refine ⟨Subtype.val '' V, Subtype.val '' W,
      hopen.isOpenMap_subtype_val _ hV, hopen.isOpenMap_subtype_val _ hW,
      ⟨a, ha, rfl⟩, ⟨b, hb', rfl⟩, ?_⟩
    apply Set.disjoint_left.mpr
    rintro z ⟨a', ha', hza⟩ ⟨b', hb'', hzb⟩
    have hab' : a' = b' := Subtype.ext (hza.trans hzb.symm)
    exact (Set.disjoint_left.mp hVW) ha' (hab'.symm ▸ hb'')
  · obtain ⟨V, W, hV, hW, hx, hy, hVW⟩ := t2_separation hb
    exact ⟨f ⁻¹' V, f ⁻¹' W, hV.preimage hf, hW.preimage hf,
      hx, hy, hVW.preimage f⟩

end Wikipedia.HopfProblem.DiagonalQuotient
