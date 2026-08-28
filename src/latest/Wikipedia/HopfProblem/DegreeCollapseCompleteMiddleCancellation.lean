import Wikipedia.HopfProblem.DegreeCollapsePreservedMiddleAdjacency
import Wikipedia.HopfProblem.DegreeCollapseIndexedMorseCancellation

/-!
# Construct a middle-pair cancellation from a complete surjective native family

The actual last index-two coordinate is primitive. Realize Euclidean
column reduction, move the resulting unit sphere first, preserve the native
belt's forward basin, and cancel the resulting consecutive pair. No signed
unit count, one-point intersection, or connecting orbit is an input.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

attribute [local irreducible] canonicalMiddleMatrix

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] [PathConnectedSpace M] {f : M → ℝ}

theorem cancel_from_complete_middle_family
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder : ∀ x y : criticalPoints E f, f x < f y →
      nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (p : criticalPoints E f)
    (hindex : Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2)
    (hnull : ∀ δ : C(Hemisphere.Sphere 1, (S.data p).LowerLevel),
      ∃ z, δ.Homotopic (ContinuousMap.const _ z))
    (hprimitive : Surjective ((S.data p).indexTwoCollapseCoordinate hf.continuous hindex))
    (hcut : ∀ z : criticalPoints E f, nativeMorseIndex E f z < 3 →
      f z < f p + (S.data p).radius ^ 2)
    {r n : ℕ} (labels : Fin n → criticalPoints E f)
    (hlabels : ∀ j, nativeMorseIndex E f (labels j) = 3)
    (hcomplete : ∀ z : criticalPoints E f, nativeMorseIndex E f z = 3 → ∃ j, labels j = z)
    (hlower : ∀ j, f p + (S.data p).radius ^ 2 < S.toSurgeryWindows.lower (labels j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ f p + (S.data p).radius ^ 2} 2)
    (γ : Fin n → C(S₂, (S.data p).UpperLevel))
    (hγ : IsNativeMiddleBasinFamily S hf (S.data p).upper_regular labels (fun j => γ j))
    (hsurj : Surjective (canonicalMiddleMatrix B γ).mulVec) :
    ∃ v : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v ∧ IsMorse E v ∧
      InjOn v (criticalPoints E v) ∧
      (criticalPoints E v).ncard + 2 = (criticalPoints E f).ncard := by
  let c := f p + (S.data p).radius ^ 2
  let L := (S.data p).indexTwoCollapseCoordinate hf.continuous hindex
  have hpold : nativeMorseIndex E f p = 2 :=
    (nativeMorseIndex_eq_chart (S.data p).chart).trans hindex
  obtain ⟨ops, -, g, hg, hmg, hcrit, hgorder, hindices, -, houtside, hgcut,
    hsub, hlevel, hga, T, -, -, hpg, hgcomplete, hglower,
    Γ, hΓ, -, -, hgsurj, ⟨i, hi⟩, hkeep⟩ :=
    S.exists_primitive_functional_unit hf hm hdim horder (S.data p).upper_regular hcut
      labels hlabels hcomplete hlower B γ hγ hsurj L hprimitive
  let pg : Fin n → criticalPoints E g :=
    fun j => ⟨(labels j).val, hcrit.symm ▸ (labels j).property⟩
  let Bg := B.trans (equalCutHomologyEquiv hsub)
  obtain ⟨u, hu, hmu, hcu, huorder, huindices, -, huoutside, hfirst,
    husub, hulevel, hua, U, -, huflow, -, hpu, hulower, hfamily, -, -, -⟩ :=
    T.exists_first_middle_pivot hg hmg hga hgorder pg hpg hgcomplete hglower Bg Γ hΓ hgsurj i
  let hcrit' := hcu.trans hcrit
  let hsub' : ∀ y, u y ≤ c ↔ f y ≤ c := fun y => (husub y).trans (hsub y)
  let hlevel' : ∀ y, u y = c ↔ f y = c := fun y => (hulevel y).trans (hlevel y)
  let q : criticalPoints E u := ⟨(labels i).val, hcrit'.symm ▸ (labels i).property⟩
  let Δ := fun j => equalCutSection hulevel (Γ j)
  have hids (z : M) (hz : z ∈ criticalPoints E f) :
      nativeMorseIndex E u z = nativeMorseIndex E f z :=
    (huindices z (hcrit.symm ▸ hz)).trans (hindices z hz)
  have hfixed (z : M) (hz : z ∈ criticalPoints E f) (hidx : nativeMorseIndex E f z ≠ 3) :
      u z = f z := by
    have hnotlabel (j : Fin n) : z ≠ (labels j).val := by
      intro heq
      apply hidx
      rw [heq]
      exact hlabels j
    exact (huoutside z (hcrit.symm ▸ hz) hnotlabel).trans (houtside z hz hnotlabel)
  have hpcrit : p.val ∈ criticalPoints E u := hcrit'.symm ▸ p.property
  have hpnew : nativeMorseIndex E u p = 2 := (hids p p.property).trans hpold
  have hq : nativeMorseIndex E u q = 3 := (hids (labels i) (labels i).property).trans (hlabels i)
  have hfirstcrit (z : criticalPoints E u) (hz : nativeMorseIndex E u z = 3) (hne : z ≠ q) :
      u q < u z := by
    let zf : criticalPoints E f := ⟨z.val, hcrit' ▸ z.property⟩
    have hzidx : nativeMorseIndex E f zf = 3 := (hids z zf.property).symm.trans hz
    obtain ⟨j, hj⟩ := hcomplete zf hzidx
    have hji : j ≠ i := by
      intro hji
      apply hne
      apply Subtype.ext
      exact (congrArg (fun z : criticalPoints E f => z.val) hj).symm.trans
        (congrArg (fun k => (labels k).val) hji)
    have hh := hfirst j hji
    change u (labels i) < u (labels j) at hh
    simpa only [hj] using hh
  have hconsecutive := consecutive_last_two_first_three S.toSurgeryWindows p hpold
    hcrit' hids hfixed hcut huorder q hq hfirstcrit
  have hpc : u p < c := by
    rw [hfixed p p.property (by omega)]
    exact S.toSurgeryWindows.value_lt_upper p
  have hcq : c < u q := (hulower i).trans (U.toSurgeryWindows.lower_lt_value q)
  have hclass := equalCutSection_class husub hulevel (Γ i)
  have hpull : (equalCutHomologyEquiv hsub').symm (middleSectionClass (Δ i)) =
      (equalCutHomologyEquiv hsub).symm (middleSectionClass (Γ i)) := by
    rw [← equalCutHomologyEquiv_trans hsub husub]
    change (equalCutHomologyEquiv hsub).symm
      ((equalCutHomologyEquiv husub).symm (middleSectionClass (Δ i))) = _
    rw [← hclass, LinearEquiv.symm_apply_apply]
  have hunit : (L ((equalCutHomologyEquiv hsub').symm (middleSectionClass (Δ i)))).natAbs = 1 := by
    rw [hpull]
    rcases hi with hi | hi <;> rw [hi] <;> norm_num
  have hforward (y : (S.data p).UpperLevel) :
      Tendsto (fun t => U.flow t y.val) atTop (𝓝 p.val) ↔
        Tendsto (fun t => S.flow t y.val) atTop (𝓝 p.val) := by
    rw [huflow]
    exact (hkeep y.val y.property.le).2.2 p.val
  let _ := RegularLevel.chartedSpace hu hua
  obtain ⟨v, hv, hmv, hcard, hcv, hext⟩ := cancel_from_preserved_unit_belt_cut
    S U hf hu hmu hdim p hindex hnull hpcrit hpnew q hq hconsecutive hpc hcq
      hsub' hlevel' hua hforward (Δ i) (hfamily.1 i) (hfamily.2.1 i).injective
        (hfamily.2.2.1 i) (hfamily.2.2.2.2 i) hunit
  obtain ⟨-, hinj, -⟩ := adapted_surgeries_after_pair_removal U.toSurgeryWindows
    ⟨p.val, hpcrit⟩ q hconsecutive hv hmv hcv hext
  refine ⟨v, hv, hmv, hinj, ?_⟩
  rwa [hcrit'] at hcard

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
