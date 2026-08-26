import ErdosProblems.Erdos1038.PlatformReferenceRefinement
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Continuity of the canonical platform reference quantile

The reference cut was initially constructed by unique choice from the
strictly increasing cumulative angular mass.  Here it is promoted to the
inverse of a homeomorphism between the two compact intervals.  In
particular the physical platform quantile is continuous, which is the
input needed for its canonical left-Riemann approximations.
-/

set_option warningAsError false

open Set

namespace Erdos1038

noncomputable section

/-- The normalized cumulative reference mass, bundled with its codomain
interval. -/
def platformReferenceCumulativeMap
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    Icc (0 : ℝ) Real.pi → Icc (0 : ℝ) 1 :=
  fun theta ↦
    ⟨platformReferenceCumulative k a theta,
      platformReferenceCumulative_mem_Icc hk ha ha2 hthreshold theta.property⟩

/-- The chosen reference cut, bundled with its angular interval. -/
def platformReferenceCutMap
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    Icc (0 : ℝ) 1 → Icc (0 : ℝ) Real.pi :=
  fun u ↦
    ⟨platformReferenceCut k a hk ha ha2 hthreshold u,
      platformReferenceCut_mem_Icc k a hk ha ha2 hthreshold u⟩

lemma platformReferenceCutMap_leftInverse
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    Function.LeftInverse
      (platformReferenceCutMap k a hk ha ha2 hthreshold)
      (platformReferenceCumulativeMap k a hk ha ha2 hthreshold) := by
  intro theta
  apply Subtype.ext
  apply (platformReferenceCumulative_strictMonoOn hk ha ha2 hthreshold).injOn
  · exact (platformReferenceCutMap k a hk ha ha2 hthreshold
      (platformReferenceCumulativeMap k a hk ha ha2 hthreshold theta)).property
  · exact theta.property
  · change platformReferenceCumulative k a
        (platformReferenceCut k a hk ha ha2 hthreshold
          (platformReferenceCumulativeMap k a hk ha ha2 hthreshold theta)) =
      platformReferenceCumulative k a theta
    exact platformReferenceCumulative_cut
      k a hk ha ha2 hthreshold
      (platformReferenceCumulativeMap k a hk ha ha2 hthreshold theta)

lemma platformReferenceCutMap_rightInverse
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    Function.RightInverse
      (platformReferenceCutMap k a hk ha ha2 hthreshold)
      (platformReferenceCumulativeMap k a hk ha ha2 hthreshold) := by
  intro u
  apply Subtype.ext
  exact platformReferenceCumulative_cut k a hk ha ha2 hthreshold u

/-- Cumulative reference mass and reference cut are inverse
equivalences of compact intervals. -/
def platformReferenceCumulativeEquiv
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    Icc (0 : ℝ) Real.pi ≃ Icc (0 : ℝ) 1 where
  toFun := platformReferenceCumulativeMap k a hk ha ha2 hthreshold
  invFun := platformReferenceCutMap k a hk ha ha2 hthreshold
  left_inv := platformReferenceCutMap_leftInverse
    k a hk ha ha2 hthreshold
  right_inv := platformReferenceCutMap_rightInverse
    k a hk ha ha2 hthreshold

theorem continuous_platformReferenceCumulativeMap
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    Continuous
      (platformReferenceCumulativeMap k a hk ha ha2 hthreshold) := by
  apply Continuous.subtype_mk
  exact continuousOn_iff_continuous_restrict.mp
    (continuous_platformReferenceCumulative k ha ha2.le)

/-- The cumulative reference mass is a homeomorphism of its angular and
probability intervals. -/
def platformReferenceCumulativeHomeomorph
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    Icc (0 : ℝ) Real.pi ≃ₜ Icc (0 : ℝ) 1 :=
  Continuous.homeoOfEquivCompactToT2
    (f := platformReferenceCumulativeEquiv k a hk ha ha2 hthreshold) (by
      change Continuous
        (platformReferenceCumulativeMap k a hk ha ha2 hthreshold)
      exact continuous_platformReferenceCumulativeMap
        k a hk ha ha2 hthreshold)

theorem continuous_platformReferenceCutMap
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    Continuous (platformReferenceCutMap k a hk ha ha2 hthreshold) := by
  simpa only [platformReferenceCumulativeHomeomorph,
    platformReferenceCumulativeEquiv] using!
      (platformReferenceCumulativeHomeomorph
        k a hk ha ha2 hthreshold).continuous_invFun

/-- The canonical physical reference quantile on `[0,1]`. -/
def platformReferenceQuantile
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (u : Icc (0 : ℝ) 1) : ℝ :=
  platformAngularDistance a
    (platformReferenceCut k a hk ha ha2 hthreshold u)

theorem continuous_platformReferenceQuantile
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    Continuous (platformReferenceQuantile k a hk ha ha2 hthreshold) := by
  have hcut : Continuous
      (fun u ↦ (platformReferenceCutMap k a hk ha ha2 hthreshold u : ℝ)) :=
    continuous_subtype_val.comp
      (continuous_platformReferenceCutMap k a hk ha ha2 hthreshold)
  unfold platformReferenceQuantile platformAngularDistance
  fun_prop

lemma platformReferenceQuantile_mem_Icc
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (u : Icc (0 : ℝ) 1) :
    platformReferenceQuantile k a hk ha ha2 hthreshold u ∈ Icc a 2 := by
  apply platformAngularDistance_mem_Icc ha2.le
  exact platformReferenceCut_mem_Icc k a hk ha ha2 hthreshold u

@[simp]
lemma platformReferenceQuantile_zero
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    platformReferenceQuantile k a hk ha ha2 hthreshold
      ⟨0, by constructor <;> norm_num⟩ = a := by
  unfold platformReferenceQuantile
  have hcut : platformReferenceCut k a hk ha ha2 hthreshold
      ⟨0, by constructor <;> norm_num⟩ = 0 := by
    apply (platformReferenceCumulative_strictMonoOn
      hk ha ha2 hthreshold).injOn
    · exact platformReferenceCut_mem_Icc k a hk ha ha2 hthreshold _
    · exact left_mem_Icc.mpr Real.pi_pos.le
    · simpa only [platformReferenceCumulative_zero] using!
        platformReferenceCumulative_cut k a hk ha ha2 hthreshold
          ⟨0, by constructor <;> norm_num⟩
  rw [hcut, platformAngularDistance_zero]

@[simp]
lemma platformReferenceQuantile_one
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    platformReferenceQuantile k a hk ha ha2 hthreshold
      ⟨1, by constructor <;> norm_num⟩ = 2 := by
  unfold platformReferenceQuantile
  have hcut : platformReferenceCut k a hk ha ha2 hthreshold
      ⟨1, by constructor <;> norm_num⟩ = Real.pi := by
    apply (platformReferenceCumulative_strictMonoOn
      hk ha ha2 hthreshold).injOn
    · exact platformReferenceCut_mem_Icc k a hk ha ha2 hthreshold _
    · exact right_mem_Icc.mpr Real.pi_pos.le
    · simpa only [platformReferenceCumulative_pi k ha ha2.le] using!
        platformReferenceCumulative_cut k a hk ha ha2 hthreshold
          ⟨1, by constructor <;> norm_num⟩
  rw [hcut, platformAngularDistance_pi]

end

end Erdos1038
