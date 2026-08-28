import Wikipedia.NoExoticSixSphere.JamesSphereGeneratorTailFamily

/-!
# The two actual cover maps are projection and generator concatenation

Move the initial point of a generator tail within the appropriate
punctured sphere. One endpoint removes the generator tail; the other
restores the whole generator. The homotopies take values in the original
path-projection inverse images throughout.
-/

noncomputable section

open scoped unitInterval ContinuousMap

namespace NoExoticSixSphere.JamesSphere.CoverMaps

abbrev Lower (n : ℕ) := EndingPath.restriction (spherePole (n + 1)) {lowerPuncture n}ᶜ
abbrev Upper (n : ℕ) := EndingPath.restriction (spherePole (n + 1)) {upperPuncture n}ᶜ
abbrev Loops (n : ℕ) := Path (spherePole (n + 1)) (spherePole (n + 1))

def lowerEquiv (n : ℕ) : Lower n ≃ₕ Loops n :=
  EndingPath.restrictionEquiv (spherePole (n + 1)) {lowerPuncture n}ᶜ
    (lowerPuncture_ne_pole n).symm
    (SpherePathCover.contraction (lowerPuncture n) ⟨_, (lowerPuncture_ne_pole n).symm⟩)

def upperEquiv (n : ℕ) : Upper n ≃ₕ Loops n :=
  EndingPath.restrictionEquiv (spherePole (n + 1)) {upperPuncture n}ᶜ
    (upperPuncture_ne_pole n).symm
    (SpherePathCover.contraction (upperPuncture n) ⟨_, (upperPuncture_ne_pole n).symm⟩)

def lowerLoops (n : ℕ) : C(Loops n, Lower n) := (lowerEquiv n).symm.toFun
def upperLoops (n : ℕ) : C(Loops n, Upper n) := (upperEquiv n).symm.toFun

theorem lowerLoops_val (n : ℕ) (p : Loops n) : (lowerLoops n p).val = EndingPath.ofPath p := rfl
theorem upperLoops_val (n : ℕ) (p : Loops n) : (upperLoops n p).val = EndingPath.ofPath p := rfl

def lowerOverlap (n : ℕ) :
    C(EndingPath.restriction (spherePole (n + 1)) (overlap n), Lower n) :=
  ContinuousMap.inclusion (fun _ hp ↦ hp.1)

def upperOverlap (n : ℕ) :
    C(EndingPath.restriction (spherePole (n + 1)) (overlap n), Upper n) :=
  ContinuousMap.inclusion (fun _ hp ↦ hp.2)

def lowerPsi (n : ℕ) : C(LoopParameter n, Lower n) :=
  (lowerOverlap n).comp (Overlap.loopProductEquiv n).symm.toFun

def upperPsi (n : ℕ) : C(LoopParameter n, Upper n) :=
  (upperOverlap n).comp (Overlap.loopProductEquiv n).symm.toFun

def lowerPrefixHomotopy (n : ℕ) : (lowerPsi n).Homotopy
    ((lowerLoops n).comp (EndingPath.constantPrefix.comp (loopProjection n))) where
  toFun p := ⟨generatorTailFamily n (Set.Icc.convexComb middleTime 1 p.1, p.2), by
    change EndingPath.source (spherePole (n + 1))
      (generatorTailFamily n (Set.Icc.convexComb middleTime 1 p.1, p.2)) ≠ lowerPuncture n
    rw [generatorTailFamily_source]
    apply upper_half_avoids_lower
    change (1 : ℝ) / 2 ≤ (1 - (p.1 : ℝ)) * ((1 : ℝ) / 2) + (p.1 : ℝ) * 1
    nlinarith [p.1.property.1]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (generatorTailFamily n).continuous.comp
      (((Set.Icc.continuous_convexComb middleTime 1).comp continuous_fst).prodMk continuous_snd)
  map_zero_left p := by
    apply Subtype.ext
    change generatorTailFamily n (Set.Icc.convexComb middleTime 1 0, p) = _
    rw [Set.Icc.convexComb_zero, generatorTailFamily_middle]
    rfl
  map_one_left p := by
    apply Subtype.ext
    change generatorTailFamily n (Set.Icc.convexComb middleTime 1 1, p) = _
    rw [Set.Icc.convexComb_one, generatorTailFamily_one]
    rfl

def lowerHomotopy (n : ℕ) :
    (lowerPsi n).Homotopy ((lowerLoops n).comp (loopProjection n)) :=
  (lowerPrefixHomotopy n).trans
    ((ContinuousMap.Homotopy.refl (lowerLoops n)).comp
      (EndingPath.constantPrefixHomotopy.compContinuousMap (loopProjection n)))

def upperHomotopy (n : ℕ) :
    (upperPsi n).Homotopy ((upperLoops n).comp (generatorAction n)) where
  toFun p := ⟨generatorTailFamily n (Set.Icc.convexComb middleTime 0 p.1, p.2), by
    change EndingPath.source (spherePole (n + 1))
      (generatorTailFamily n (Set.Icc.convexComb middleTime 0 p.1, p.2)) ≠ upperPuncture n
    rw [generatorTailFamily_source]
    apply lower_half_avoids_upper
    change (1 - (p.1 : ℝ)) * ((1 : ℝ) / 2) + (p.1 : ℝ) * 0 ≤ 1 / 2
    nlinarith [p.1.property.1]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (generatorTailFamily n).continuous.comp
      (((Set.Icc.continuous_convexComb middleTime 0).comp continuous_fst).prodMk continuous_snd)
  map_zero_left p := by
    apply Subtype.ext
    change generatorTailFamily n (Set.Icc.convexComb middleTime 0 0, p) = _
    rw [Set.Icc.convexComb_zero, generatorTailFamily_middle]
    rfl
  map_one_left p := by
    apply Subtype.ext
    change generatorTailFamily n (Set.Icc.convexComb middleTime 0 1, p) = _
    rw [Set.Icc.convexComb_one, generatorTailFamily_zero]
    rfl

end NoExoticSixSphere.JamesSphere.CoverMaps
