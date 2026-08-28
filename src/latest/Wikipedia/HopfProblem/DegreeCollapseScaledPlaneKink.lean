import Wikipedia.HopfProblem.DegreeCollapsePlaneKinkTransversality
import Wikipedia.HopfProblem.DegreeCollapseKinkPlaneCoordinates

/-!
# Rescaling the actual compact plane modification

Both domain and target are rescaled by the same nonzero scalar. Exact
agreement with the literal plane is retained, with the actual compact
support and the two original model preimages rescaled accordingly.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SupportedCusp

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization WhitneyCusp

def scaledMap (β : Cutoff) (ε : ℝ) (t : ℝ) (x : Vector 3) : Vector 6 :=
  ε • longMap β t (ε⁻¹ • x)

def scaledSupport (β : Cutoff) (ε : ℝ) : Set (Vector 3) := (fun x ↦ ε • x) '' longSupport β

theorem isCompact_scaledSupport (β : Cutoff) (ε : ℝ) : IsCompact (scaledSupport β ε) :=
  (isCompact_longSupport β).image (by fun_prop)

theorem contDiff_scaledMap (β : Cutoff) (ε : ℝ) : ContDiff ℝ ∞ (uncurry (scaledMap β ε)) := by
  have h : ContDiff ℝ ∞ (fun p : ℝ × Vector 3 ↦ (p.1, ε⁻¹ • p.2)) :=
    contDiff_fst.prodMk (contDiff_snd.const_smul _)
  exact ((contDiff_longMap β).comp h).const_smul ε

theorem contDiff_scaledMap_slice (β : Cutoff) (ε t : ℝ) :
    ContDiff ℝ ∞ (scaledMap β ε t) := by
  have h : ContDiff ℝ ∞ (fun x : Vector 3 ↦ (t, x)) := contDiff_const.prodMk contDiff_id
  have hcomp := (contDiff_scaledMap β ε).comp h
  exact hcomp

theorem scaledMap_smul (β : Cutoff) {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) (x : Vector 3) :
    scaledMap β ε t (ε • x) = ε • longMap β t x := by
  rw [scaledMap, inv_smul_smul₀ hε]

theorem scaledMap_neg_one (β : Cutoff) {ε : ℝ} (hε : ε ≠ 0) (x : Vector 3) :
    scaledMap β ε (-1) x = plane x := by
  rw [scaledMap, longMap_neg_one, plane_smul, smul_inv_smul₀ hε]

theorem scaledMap_eq_plane_off_support (β : Cutoff) {ε : ℝ} (hε : ε ≠ 0)
    (t : ℝ) {x : Vector 3} (hx : x ∉ scaledSupport β ε) : scaledMap β ε t x = plane x := by
  have hu : ε⁻¹ • x ∉ longSupport β := fun hu ↦ hx ⟨ε⁻¹ • x, hu, smul_inv_smul₀ hε x⟩
  rw [scaledMap, longMap_eq_plane_off_support β t hu, plane_smul, smul_inv_smul₀ hε]

theorem scaledMap_endpoint_eq_iff (β : Cutoff) {ε : ℝ} (hε : ε ≠ 0) (x y : Vector 3) :
    scaledMap β ε 1 x = scaledMap β ε 1 y ↔ x = y ∨
      (x = ε • sourceDiffeomorph (axis 1) ∧ y = ε • sourceDiffeomorph (axis (-1))) ∨
      (x = ε • sourceDiffeomorph (axis (-1)) ∧ y = ε • sourceDiffeomorph (axis 1)) := by
  constructor
  · intro h
    have h' : longMap β 1 (ε⁻¹ • x) = longMap β 1 (ε⁻¹ • y) := by
      have hh := congrArg (fun v : Vector 6 ↦ ε⁻¹ • v) h
      simpa only [scaledMap, inv_smul_smul₀ hε] using hh
    rcases (longMap_endpoint_eq_iff β _ _).mp h' with hxy | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · left
      have hh := congrArg (fun v : Vector 3 ↦ ε • v) hxy
      simpa only [smul_inv_smul₀ hε] using hh
    · right
      left
      exact ⟨(smul_inv_smul₀ hε x).symm.trans (congrArg (fun v ↦ ε • v) hx),
        (smul_inv_smul₀ hε y).symm.trans (congrArg (fun v ↦ ε • v) hy)⟩
    · right
      right
      exact ⟨(smul_inv_smul₀ hε x).symm.trans (congrArg (fun v ↦ ε • v) hx),
        (smul_inv_smul₀ hε y).symm.trans (congrArg (fun v ↦ ε • v) hy)⟩
  · have hc : longMap β 1 (sourceDiffeomorph (axis 1)) =
        longMap β 1 (sourceDiffeomorph (axis (-1))) :=
      (longMap_endpoint_eq_iff β _ _).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · rw [scaledMap_smul β hε, scaledMap_smul β hε, hc]
    · rw [scaledMap_smul β hε, scaledMap_smul β hε, hc]

end Wikipedia.HopfProblem.DegreeCollapse.SupportedCusp
