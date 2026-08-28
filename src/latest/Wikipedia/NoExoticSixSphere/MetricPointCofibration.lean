import Wikipedia.NoExoticSixSphere.OpenHomotopyExtension
import Wikipedia.HopfProblem.OrbitPairNeighborhoodHomotopyExtension
import Mathlib.Topology.MetricSpace.Basic

/-!+# A point cofibration from a specified local contraction

A strong contraction on an open neighborhood containing the closed unit
ball gives explicit neighborhood-deformation data for the point. A time
cutoff is one on the half ball and vanishes outside the unit ball.
-/

noncomputable section

universe u

open CategoryTheory Set Topology unitInterval
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.MetricPointCofibration

variable {X : Type u} [MetricSpace X] (b : X)

def inclusion : TopCat.of ({b} : Set X) ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

def height : C(X, I) where
  toFun x := ⟨min 1 (2 * dist x b),
    le_min zero_le_one (mul_nonneg (by norm_num) dist_nonneg), min_le_left _ _⟩
  continuous_toFun :=
    (continuous_const.min (continuous_const.mul (continuous_id.dist continuous_const))).subtype_mk _

theorem height_zero_iff (x : X) : height b x = 0 ↔ x = b := by
  constructor
  · intro h
    have hm : min 1 (2 * dist x b) = 0 := congrArg Subtype.val h
    have hd : dist x b = 0 := by
      rcases le_total 1 (2 * dist x b) with hle | hle
      · rw [min_eq_left hle] at hm
        norm_num at hm
      · rw [min_eq_right hle] at hm
        linarith
    exact dist_eq_zero.mp hd
  · rintro rfl
    apply Subtype.ext
    simp [height]

theorem height_lt_one (x : X) (hx : height b x < 1) : dist x b < 1 / 2 := by
  have hm : min 1 (2 * dist x b) < 1 := hx
  have hd : 2 * dist x b < 1 := (min_lt_iff.mp hm).resolve_left (lt_irrefl _)
  linarith

def cutoff : C(X, ℝ) :=
  ⟨fun x ↦ max 0 (min 1 (2 - 2 * dist x b)),
    continuous_const.max (continuous_const.min
      (continuous_const.sub (continuous_const.mul (continuous_id.dist continuous_const))))⟩

theorem cutoff_mem (x : X) : cutoff b x ∈ I :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem cutoff_zero (x : X) (hx : 1 ≤ dist x b) : cutoff b x = 0 := by
  change max 0 (min 1 (2 - 2 * dist x b)) = 0
  apply max_eq_left
  exact (min_le_right _ _).trans (by linarith)

theorem cutoff_one (x : X) (hx : dist x b ≤ 1 / 2) : cutoff b x = 1 := by
  change max 0 (min 1 (2 - 2 * dist x b)) = 1
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem cutoff_support : tsupport (cutoff b) ⊆ Metric.closedBall b 1 := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  apply Metric.mem_closedBall.mpr
  by_contra hn
  exact hx (cutoff_zero b x (le_of_lt (lt_of_not_ge hn)))

variable {U : Set X} (hU : IsOpen U) (hball : Metric.closedBall b 1 ⊆ U)
    (H : C(I × U, X)) (h0 : ∀ x : U, H (0, x) = x.val)
    (hfixed : ∀ t (x : U), x.val = b → H (t, x) = b)
    (h1 : ∀ x : U, H (1, x) = b)

def deformation : C(I × X, X) :=
  OpenHomotopyExtension.map H (cutoff b) (cutoff_mem b) h0 hU
    ((cutoff_support b).trans hball)

theorem deformation_zero (x : X) : deformation b hU hball H h0 (0, x) = x :=
  OpenHomotopyExtension.raw_zero H (cutoff b) (cutoff_mem b) h0 x

include hfixed in
theorem deformation_fixed (t : I) : deformation b hU hball H h0 (t, b) = b := by
  have hb : b ∈ U := hball (Metric.mem_closedBall.mpr (by simp))
  change OpenHomotopyExtension.raw H (cutoff b) (cutoff_mem b) (t, b) = b
  rw [OpenHomotopyExtension.raw_of_mem H (cutoff b) (cutoff_mem b) hb]
  exact hfixed _ _ rfl

include h1 in
theorem deformation_terminal (x : X) (hx : height b x < 1) :
    deformation b hU hball H h0 (1, x) = b := by
  have hd := height_lt_one b x hx
  have hxu : x ∈ U := hball (Metric.mem_closedBall.mpr (by linarith))
  change OpenHomotopyExtension.raw H (cutoff b) (cutoff_mem b) (1, x) = b
  rw [OpenHomotopyExtension.raw_of_mem H (cutoff b) (cutoff_mem b) hxu,
    CutoffHomotopyGluing.clock_one_of_one (cutoff b) (cutoff_mem b)
      (cutoff_one b x hd.le)]
  exact h1 _

def data : NeighborhoodDeformation.Data (inclusion b) where
  height := height b
  deformation := deformation b hU hball H h0
  zero_iff x := by
    rw [height_zero_iff]
    constructor
    · intro hx
      rw [hx]
      exact ⟨⟨b, rfl⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact a.property
  bottom := deformation_zero b hU hball H h0
  fixed t a := by
    have ha : a.val = b := a.property
    change deformation b hU hball H h0 (t, a.val) = a.val
    rw [ha]
    exact deformation_fixed b hU hball H h0 hfixed t
  terminal x hx := by
    rw [deformation_terminal b hU hball H h0 h1 x hx]
    exact ⟨⟨b, rfl⟩, rfl⟩

include hU hball h0 hfixed h1 in
theorem hasHomotopyExtension : HomotopyExtension.HasHomotopyExtension (inclusion b) :=
  NeighborhoodDeformation.hasHomotopyExtension (data b hU hball H h0 hfixed h1)
    IsEmbedding.subtypeVal

end NoExoticSixSphere.MetricPointCofibration
