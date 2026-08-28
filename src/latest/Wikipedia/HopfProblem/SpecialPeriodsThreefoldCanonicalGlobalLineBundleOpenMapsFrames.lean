import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleOpenMaps
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleOpenMapsFramesAlgebra
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleOpenMapsFramesHolomorphic

/-!
# Actual holomorphic frame-to-frame maps over an open set

Two genuine holomorphic nonvanishing sections on an open set define a
native bundle map by their preferred-coordinate ratio. The multiplier
is extended by the unit one outside that open set; no assertion of
holomorphicity there is made. On the open set the map is holomorphic,
sends the first actual section to the second, and has holomorphic
inverse. Its extracted chart units are exactly the ratios of the two
actual local frame coefficients.
-/

noncomputable section

open Bundle Set Topology TopologicalSpace
open scoped ContDiff

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle.OpenMaps

open HolomorphicCharacterBundle

variable {M ι η : Type*} [TopologicalSpace M]
  (A : TransitionData M ι) (B : TransitionData M η)

section Algebra

variable (U : Opens M) (s : ∀ x, A.core.Fiber x) (t : ∀ x, B.core.Fiber x)
  (hs : ∀ x ∈ U, s x ≠ 0) (ht : ∀ x ∈ U, t x ≠ 0)

/-- The native map sends the given genuine source frame to the given
genuine target frame on their actual common domain. -/
theorem preferredMap_frameMultiplier_frame {x : M} (hx : x ∈ U) :
    preferredMap A B (frameMultiplier A B U s t hs ht) ⟨x, s x⟩ = ⟨x, t x⟩ :=
  frameMultiplier_frame A B U s t hs ht hx

/-- Its actual local coefficient is the quotient of the two native
frame coefficients times the original source coefficient. -/
theorem preferredMap_frameMultiplier_localCoefficient (i : ι × η)
    (p : A.core.TotalSpace) (hp : p.proj ∈ U) :
    (B.core.localTriv i.2
      (preferredMap A B (frameMultiplier A B U s t hs ht) p)).2 =
      (B.localCoefficient t i.2 p.proj / A.localCoefficient s i.1 p.proj) *
        (A.core.localTriv i.1 p).2 :=
  frameMultiplier_localCoefficient A B U s t hs ht i.1 i.2 p hp

/-- The extracted gauge unit is exactly the ratio of actual target and
source frame coefficients in the independently chosen original charts. -/
theorem chartUnit_frameMultiplier_ratio (i : ι × η) {x : M}
    (hx : x ∈ U) (hi : x ∈ A.baseSet i.1 ∩ B.baseSet i.2) :
    (chartUnit A B (frameMultiplier A B U s t hs ht) i x : ℂ) =
      B.localCoefficient t i.2 x / A.localCoefficient s i.1 x := by
  have hc := preferredMap_localCoefficient A B (frameMultiplier A B U s t hs ht)
    i ⟨x, s x⟩ hi
  rw [preferredMap_frameMultiplier_frame A B U s t hs ht hx] at hc
  change B.localCoefficient t i.2 x =
    (chartUnit A B (frameMultiplier A B U s t hs ht) i x : ℂ) *
      A.localCoefficient s i.1 x at hc
  exact (eq_div_iff (localCoefficient_ne_zero_of_frame A s i.1 (hs x hx))).mpr hc.symm

end Algebra

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  [ChartedSpace H M] (I : ModelWithCorners ℂ E H)
  [A.IsHolomorphic I] [B.IsHolomorphic I]

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- Nonvanishing holomorphic frames give a holomorphic map between the
actual native bundle total spaces over the specified open set. -/
theorem preferredMap_frameMultiplier_holomorphicOn
    (U : Opens M) (s : ∀ x, A.core.Fiber x) (t : ∀ x, B.core.Fiber x)
    (hs : ∀ x ∈ U, s x ≠ 0) (ht : ∀ x ∈ U, t x ≠ 0)
    (hsHol : ContMDiffOn I (I.prod I₁) ω
      (fun x => (⟨x, s x⟩ : A.core.TotalSpace)) (U : Set M))
    (htHol : ContMDiffOn I (I.prod I₁) ω
      (fun x => (⟨x, t x⟩ : B.core.TotalSpace)) (U : Set M)) :
    ContMDiffOn (I.prod I₁) (I.prod I₁) ω
      (preferredMap A B (frameMultiplier A B U s t hs ht))
      ((Bundle.TotalSpace.proj : A.core.TotalSpace → M) ⁻¹' (U : Set M)) :=
  nativeScalarMap_holomorphicOn_of_frame_ratios I A B U
    (frameMultiplier A B U s t hs ht) s t hs hsHol htHol
    (frameMultiplier_localCoefficient A B U s t hs ht)

/-- The reciprocal preferred-coordinate map is also holomorphic over
the same actual open, obtained by exchanging the two genuine frames. -/
theorem preferredMap_frameMultiplier_inv_holomorphicOn
    (U : Opens M) (s : ∀ x, A.core.Fiber x) (t : ∀ x, B.core.Fiber x)
    (hs : ∀ x ∈ U, s x ≠ 0) (ht : ∀ x ∈ U, t x ≠ 0)
    (hsHol : ContMDiffOn I (I.prod I₁) ω
      (fun x => (⟨x, s x⟩ : A.core.TotalSpace)) (U : Set M))
    (htHol : ContMDiffOn I (I.prod I₁) ω
      (fun x => (⟨x, t x⟩ : B.core.TotalSpace)) (U : Set M)) :
    ContMDiffOn (I.prod I₁) (I.prod I₁) ω
      (preferredMap B A (fun x => (frameMultiplier A B U s t hs ht x)⁻¹))
      ((Bundle.TotalSpace.proj : B.core.TotalSpace → M) ⁻¹' (U : Set M)) := by
  have he : frameMultiplier B A U t s ht hs =
      fun x => (frameMultiplier A B U s t hs ht x)⁻¹ :=
    funext (frameMultiplier_symm A B U s t hs ht)
  rw [← he]
  exact preferredMap_frameMultiplier_holomorphicOn B A I U t s ht hs htHol hsHol

/-- The local unit coefficients extracted from this actual frame map
are holomorphic on every original chart-pair intersection in the open set. -/
theorem chartUnit_frameMultiplier_holomorphicOn
    (U : Opens M) (s : ∀ x, A.core.Fiber x) (t : ∀ x, B.core.Fiber x)
    (hs : ∀ x ∈ U, s x ≠ 0) (ht : ∀ x ∈ U, t x ≠ 0)
    (hsHol : ContMDiffOn I (I.prod I₁) ω
      (fun x => (⟨x, s x⟩ : A.core.TotalSpace)) (U : Set M))
    (htHol : ContMDiffOn I (I.prod I₁) ω
      (fun x => (⟨x, t x⟩ : B.core.TotalSpace)) (U : Set M)) (i : ι × η) :
    ContMDiffOn I I₁ ω
      (fun x => (chartUnit A B (frameMultiplier A B U s t hs ht) i x : ℂ))
      ((A.baseSet i.1 ∩ B.baseSet i.2) ∩ U) :=
  chartUnit_holomorphicOn A B (frameMultiplier A B U s t hs ht) I U
    (preferredMap_frameMultiplier_holomorphicOn A B I U s t hs ht hsHol htHol) i

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle.OpenMaps
