import Wikipedia.SmoothSixDPoincare.InwardBoundaryCollar
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Tactic.Linarith

/-!
# Construct an inward collar from an exact height chart

The closed inward cylinder is the height interval from zero to minus half
the chart radius. Its open-ended image is exactly the corresponding open
height strip in the original sublevel, not merely a neighborhood in a chart.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.HeightChartInwardCollar

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : Y → ℝ} {b : ℝ}

def levelInclusion (i : C(X, Y)) (hlevel : ∀ x, f (i x) = b) : C(X, {y : Y // f y ≤ b}) :=
  ⟨fun x => ⟨i x, (hlevel x).le⟩, i.continuous.subtype_mk _⟩

variable (ε : ℝ)

def coordinates (q : X × unitInterval) : X × ℝ := (q.1, -(ε / 2) * (q.2 : ℝ))

theorem continuous_coordinates : Continuous (coordinates (X := X) ε) :=
  continuous_fst.prodMk (continuous_const.mul (continuous_subtype_val.comp continuous_snd))

variable (e : OpenPartialHomeomorph (X × ℝ) Y) (hε : 0 < ε)
  (hsource : (univ : Set X) ×ˢ closedBall (0 : ℝ) ε ⊆ e.source)
  (hheight : ∀ z ∈ e.source, f (e z) = b + z.2)

include hε hsource in
theorem coordinates_mem_source (q : X × unitInterval) : coordinates ε q ∈ e.source := by
  apply hsource
  refine ⟨mem_univ _, ?_⟩
  rw [mem_closedBall, Real.dist_eq, sub_zero, abs_le]
  have ht₀ := q.2.property.1
  have ht₁ := q.2.property.2
  change -ε ≤ -(ε / 2) * (q.2 : ℝ) ∧ -(ε / 2) * (q.2 : ℝ) ≤ ε
  constructor <;> nlinarith

include hε hsource hheight in
theorem coordinates_height (q : X × unitInterval) :
    f (e (coordinates ε q)) = b - (ε / 2) * (q.2 : ℝ) := by
  simpa only [coordinates, neg_mul, sub_eq_add_neg] using
    hheight (coordinates ε q) (coordinates_mem_source ε e hε hsource q)

def map : C(X × unitInterval, {y : Y // f y ≤ b}) := by
  refine ⟨fun q => ⟨e (coordinates ε q), ?_⟩, ?_⟩
  · rw [coordinates_height ε e hε hsource hheight]
    exact sub_le_self _ (mul_nonneg (half_pos hε).le q.2.property.1)
  · exact (e.continuousOn.comp_continuous (continuous_coordinates ε)
      (coordinates_mem_source ε e hε hsource)).subtype_mk _

theorem map_height (q : X × unitInterval) :
    f (map ε e hε hsource hheight q).val = b - (ε / 2) * (q.2 : ℝ) :=
  coordinates_height ε e hε hsource hheight q

theorem map_injective : Injective (map ε e hε hsource hheight) := by
  intro q r hqr
  have h := e.injOn (coordinates_mem_source ε e hε hsource q)
    (coordinates_mem_source ε e hε hsource r) (congrArg Subtype.val hqr)
  apply Prod.ext
  · exact congrArg (fun p : X × ℝ => p.1) h
  · apply Subtype.ext
    have ht := congrArg Prod.snd h
    change -(ε / 2) * (q.2 : ℝ) = -(ε / 2) * (r.2 : ℝ) at ht
    nlinarith

theorem map_zero (i : C(X, Y)) (hlevel : ∀ x, f (i x) = b)
    (hzero : ∀ x, e (x, 0) = i x) (x : X) :
    map ε e hε hsource hheight (x, 0) = levelInclusion i hlevel x := by
  apply Subtype.ext
  change e (x, -(ε / 2) * (0 : ℝ)) = i x
  simpa only [mul_zero] using hzero x

theorem inner_image (hband : f ⁻¹' ball b ε ⊆ e.target) :
    map ε e hε hsource hheight '' {q : X × unitInterval | q.2 < 1} =
      {y : {y : Y // f y ≤ b} | b - ε / 2 < f y.val} := by
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    change b - ε / 2 < f (map ε e hε hsource hheight q).val
    rw [map_height ε e hε hsource hheight q]
    have ht : (q.2 : ℝ) < 1 := hq
    nlinarith
  · intro hy
    have hy' : b - ε / 2 < f y.val := hy
    have hyb := y.property
    have htarget : y.val ∈ e.target := by
      apply hband
      change f y.val ∈ ball b ε
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    let z := e.symm y.val
    have hz : z ∈ e.source := e.map_target htarget
    have htz : z.2 = f y.val - b := by
      have hh := hheight z hz
      have he : e z = y.val := e.right_inv htarget
      rw [he] at hh
      linarith
    let t : unitInterval := ⟨(b - f y.val) / (ε / 2),
      div_nonneg (sub_nonneg.mpr hyb) (half_pos hε).le,
      (div_le_one (half_pos hε)).mpr (by linarith)⟩
    have ht : t < 1 := (div_lt_one (half_pos hε)).mpr (by linarith)
    have hprod : (b - f y.val) = (t : ℝ) * (ε / 2) :=
      (div_eq_iff (half_pos hε).ne').mp rfl
    have hc : coordinates ε (z.1, t) = z := by
      apply Prod.ext
      · rfl
      · change -(ε / 2) * (t : ℝ) = z.2
        nlinarith
    refine ⟨(z.1, t), ht, ?_⟩
    apply Subtype.ext
    change e (coordinates ε (z.1, t)) = y.val
    rw [hc]
    exact e.right_inv htarget

variable [CompactSpace X] [T2Space Y]

def collar (hf : Continuous f) (i : C(X, Y)) (hlevel : ∀ x, f (i x) = b)
    (hzero : ∀ x, e (x, 0) = i x) (hband : f ⁻¹' ball b ε ⊆ e.target) :
    InwardBoundaryCollar (levelInclusion i hlevel) where
  map := map ε e hε hsource hheight
  closedEmbedding := (map ε e hε hsource hheight).continuous.isClosedEmbedding
    (map_injective ε e hε hsource hheight)
  zero := map_zero ε e hε hsource hheight i hlevel hzero
  inner_open := by
    rw [inner_image ε e hε hsource hheight hband]
    exact isOpen_lt continuous_const (hf.comp continuous_subtype_val)

end Wikipedia.SmoothSixDPoincare.HeightChartInwardCollar
