import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfStableNonzero

/-!
# Every map at a stable sixth-stem stage is null or homotopic to any nonnull map

The two-value calculation is applied at a fixed actual native stage.
The original equivalence with unbased sphere-map homotopy classes then
gives a dichotomy for literal continuous maps. This avoids identifying
the ordinary suspension transition with the cubical product transition.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.SixthStemMapDichotomy

open NoExoticSixSphere CubicalStableSix StableSixSphereMaps

theorem native_eq_one_or_given (k : ℕ) (hk : 6 ≤ k) (u v : NativeStage k) (hv : v ≠ 1) :
    u = 1 ∨ u = v := by
  have hv' : CubicalStableSix.ofNative v ≠ 1 :=
    fun h ↦ hv ((ofNative_eq_one_iff_native hk v).mp h)
  have hvSquare := (SixthStemTwoValues.stable_eq_one_or_polynomial_square
    (CubicalStableSix.ofNative v)
    ).resolve_left hv'
  rcases SixthStemTwoValues.stable_eq_one_or_polynomial_square
    (CubicalStableSix.ofNative u) with hu | hu
  · exact Or.inl ((ofNative_eq_one_iff_native hk u).mp hu)
  · exact Or.inr (CubicalStableSix.ofNative_injective hk (hu.trans hvSquare.symm))

theorem nullhomotopic_or_homotopic (k : ℕ) (hk : 6 ≤ k) (f g : StageMap k)
    (hg : ¬ g.Nullhomotopic) : f.Nullhomotopic ∨ f.Homotopic g := by
  let u : NativeStage k := (nativeStageEquiv k).symm (classOf f)
  let v : NativeStage k := (nativeStageEquiv k).symm (classOf g)
  have hv : v ≠ 1 := by
    intro h
    apply hg
    apply (classOf_eq_stageZero_iff g).mp
    calc
      classOf g = nativeStageEquiv k v := (Equiv.apply_symm_apply _ _).symm
      _ = nativeStageEquiv k 1 := congrArg (nativeStageEquiv k) h
      _ = stageZero k := nativeStageEquiv_one k
  rcases native_eq_one_or_given k hk u v hv with hu | huv
  · left
    apply (classOf_eq_stageZero_iff f).mp
    calc
      classOf f = nativeStageEquiv k u := (Equiv.apply_symm_apply _ _).symm
      _ = nativeStageEquiv k 1 := congrArg (nativeStageEquiv k) hu
      _ = stageZero k := nativeStageEquiv_one k
  · right
    apply (classOf_eq_iff f g).mp
    calc
      classOf f = nativeStageEquiv k u := (Equiv.apply_symm_apply _ _).symm
      _ = nativeStageEquiv k v := congrArg (nativeStageEquiv k) huv
      _ = classOf g := Equiv.apply_symm_apply _ _

theorem nullhomotopic_of_not_homotopic (k : ℕ) (hk : 6 ≤ k) (f g : StageMap k)
    (hg : ¬ g.Nullhomotopic) (hfg : ¬ f.Homotopic g) : f.Nullhomotopic :=
  (nullhomotopic_or_homotopic k hk f g hg).resolve_right hfg

theorem nullhomotopic_of_not_homotopic_of_dimensions {m n : ℕ}
    (k : ℕ) (hk : 6 ≤ k) (hm : m = k + 8) (hn : n = k + 2)
    (f g : C(Sphere m, Sphere n)) (hg : ¬ g.Nullhomotopic) (hfg : ¬ f.Homotopic g) :
    f.Nullhomotopic := by
  subst m
  subst n
  exact nullhomotopic_of_not_homotopic k hk f g hg hfg

end Wikipedia.HopfProblem.DegreeCollapse.SixthStemMapDichotomy
