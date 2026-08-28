import Wikipedia.HopfProblem.DegreeCollapseBoundedFourFunctionalUnit
import Wikipedia.HopfProblem.DegreeCollapsePreservedThreeBeltCancellation

/-!
# An actual three/four pair cancels from the complete bounded native family

Realize a unit of the original primitive three-handle collapse coordinate
on an actual four-handle sphere. Move that sphere first with the same flow.
The preserved lower germ and native critical isolation prove consecutivity
to the original three-handle. The preserved-belt cancellation then removes
exactly this pair and fixes the full original upper germ and strict sublevel.
No unit count, transverse intersection, or connecting orbit is an input.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

attribute [local irreducible] canonicalFourMatrix

local notation "S₃" => Hemisphere.Sphere 3

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] in
theorem consecutive_at_preserved_upper_cut (S : SurgeryWindows E f)
    (p : criticalPoints E f) {g : M → ℝ}
    (hcrit : criticalPoints E g = criticalPoints E f)
    (hsub : ∀ y, g y ≤ S.upper p ↔ f y ≤ S.upper p)
    (hfixed : ∀ y, f y ≤ S.upper p → g y = f y)
    {b : ℝ} {n : ℕ} (labels : Fin n → criticalPoints E g)
    (hcomplete : ∀ z : criticalPoints E g, S.upper p < g z → g z < b →
      ∃ j, labels j = z)
    (i : Fin n) (hqb : g (labels i) < b)
    (hfirst : ∀ j, j ≠ i → g (labels i) < g (labels j)) :
    ∀ z : criticalPoints E g, ¬(g p < g z ∧ g z < g (labels i)) := by
  have hgp : g p = f p := hfixed p (S.value_lt_upper p).le
  intro z hz
  by_cases hle : g z ≤ S.upper p
  · have hfz : g z = f z := hfixed z ((hsub z).mp hle)
    have hpz : f p < f z := by rw [← hgp, ← hfz]; exact hz.1
    have he := S.isolated p z.val (hcrit ▸ z.property)
      ⟨((S.lower_lt_value p).trans hpz).le, (hsub z).mp hle⟩
    exact hz.1.ne (congrArg g he.symm)
  · obtain ⟨j, rfl⟩ := hcomplete z (lt_of_not_ge hle) (hz.2.trans hqb)
    by_cases hji : j = i
    · subst j
      exact lt_irrefl _ hz.2
    · exact (hfirst j hji).not_gt hz.2

variable [PreconnectedSpace M]

theorem cancel_from_complete_four_family
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (hdim : Module.finrank ℝ E = 7)
    (p : criticalPoints E f)
    (hindex : Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 3)
    (hnull : ∀ δ : C(Hemisphere.Sphere 1, (S.data p).LowerLevel),
      ∃ z, δ.Homotopic (ContinuousMap.const _ z))
    (hprimitive : Surjective (MiddleBasis.collapseCoordinate (S.data p) 1 hf.continuous hindex))
    {b : ℝ} (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    (m : criticalPoints E f)
    (hprefix : ∀ z : criticalPoints E f, f z < b → z = m ∨
      nativeMorseIndex E f z = 3 ∨ nativeMorseIndex E f z = 4)
    {r n : ℕ} (labels : Fin n → criticalPoints E f)
    (hlabels : ∀ j, nativeMorseIndex E f (labels j) = 4)
    (hvalues : ∀ j, f p + (S.data p).radius ^ 2 < f (labels j) ∧ f (labels j) < b)
    (hcomplete : ∀ z : criticalPoints E f,
      f p + (S.data p).radius ^ 2 < f z → f z < b → ∃ j, labels j = z)
    (B : (Fin r → ℤ) ≃ₗ[ℤ]
      SingularHomology {y : M // f y ≤ f p + (S.data p).radius ^ 2} 3)
    (γ : Fin n → C(S₃, (S.data p).UpperLevel))
    (hγ : IsNativeFourBasinFamily S hf (S.data p).upper_regular labels (fun j => γ j))
    (hsurj : Surjective (canonicalFourMatrix B γ).mulVec) :
    ∃ i : Fin n, ∃ v : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v ∧ IsMorse E v ∧
      InjOn v (criticalPoints E v) ∧
      (criticalPoints E v).ncard + 2 = (criticalPoints E f).ncard ∧
      (∀ z, z ∈ criticalPoints E v ↔
        z ∈ criticalPoints E f ∧ z ≠ p.val ∧ z ≠ (labels i).val) ∧
      (∀ z ∈ criticalPoints E v, nativeMorseIndex E v z = nativeMorseIndex E f z) ∧
      (∀ z, b ≤ f z → v =ᶠ[𝓝 z] f) ∧ ∀ z, v z < b ↔ f z < b := by
  let c := f p + (S.data p).radius ^ 2
  let L := MiddleBasis.collapseCoordinate (S.data p) 1 hf.continuous hindex
  have hpold : nativeMorseIndex E f p = 3 :=
    (nativeMorseIndex_eq_chart (S.data p).chart).trans hindex
  obtain ⟨ops, -, g, hg, hmg, hcrit, -, hindices, -, -, -, hsub, hlevel,
    hstrict, -, hlowgerm, huppergerm, hga, hgb, T, -, hpg, hgcomplete,
    hglower, hgupper, Γ, hΓ, -, -, hgsurj, ⟨i, hi⟩, hkeep⟩ :=
    S.exists_bounded_four_functional_unit hf hm hdim (S.data p).upper_regular hb m hprefix
      labels hlabels hvalues hcomplete B γ hγ hsurj L hprimitive
  let pg : Fin n → criticalPoints E g :=
    fun j => ⟨(labels j).val, hcrit.symm ▸ (labels j).property⟩
  let Bg := B.trans (equalFourCutHomologyEquiv hsub)
  have hgvalues (j : Fin n) : c < g (pg j) ∧ g (pg j) < b :=
    ⟨(hglower j).trans (T.toSurgeryWindows.lower_lt_value (pg j)),
      (T.toSurgeryWindows.value_lt_upper (pg j)).trans (hgupper j)⟩
  obtain ⟨u, hu, hmu, hcu, -, huindices, -, -, hfirst, husub, hulevel,
    hustrict, -, hulowgerm, huuppergerm, hua, -, U, -, huflow, hpu,
    hucomplete, hulower, huupper, hfamily, -, -, -⟩ :=
    T.exists_bounded_first_four_pivot hg hmg hga hgb pg hpg hgvalues hgcomplete
      Bg Γ hΓ hgsurj i
  let hcrit' := hcu.trans hcrit
  let hsub' : ∀ y, u y ≤ c ↔ f y ≤ c := fun y => (husub y).trans (hsub y)
  let hlevel' : ∀ y, u y = c ↔ f y = c := fun y => (hulevel y).trans (hlevel y)
  have hstrict' (y : M) : u y < b ↔ f y < b := (hustrict y).trans (hstrict y)
  have hlow' (y : M) (hy : f y ≤ c) : u =ᶠ[𝓝 y] f :=
    (hulowgerm y ((hsub y).mpr hy)).trans (hlowgerm y hy)
  have hupper' (y : M) (hy : b ≤ f y) : u =ᶠ[𝓝 y] f := by
    have hgy : b ≤ g y := le_of_not_gt (fun h => hy.not_gt ((hstrict y).mp h))
    exact (huuppergerm y hgy).trans (huppergerm y hy)
  let pu : Fin n → criticalPoints E u :=
    fun j => ⟨(labels j).val, hcrit'.symm ▸ (labels j).property⟩
  let q := pu i
  let Δ := fun j => equalFourCutSection hulevel (Γ j)
  have hids (z : M) (hz : z ∈ criticalPoints E f) :
      nativeMorseIndex E u z = nativeMorseIndex E f z :=
    (huindices z (hcrit.symm ▸ hz)).trans (hindices z hz)
  have hpcrit : p.val ∈ criticalPoints E u := hcrit'.symm ▸ p.property
  have hpnew : nativeMorseIndex E u p = 3 := (hids p p.property).trans hpold
  have hq : nativeMorseIndex E u q = 4 := hpu i
  have hqb : u q < b := (U.toSurgeryWindows.value_lt_upper q).trans (huupper i)
  have hconsecutive := consecutive_at_preserved_upper_cut S.toSurgeryWindows p hcrit' hsub'
    (fun y hy => (hlow' y hy).self_of_nhds) pu hucomplete i hqb hfirst
  have hpc : u p < c := by
    rw [(hlow' p (S.toSurgeryWindows.value_lt_upper p).le).self_of_nhds]
    exact S.toSurgeryWindows.value_lt_upper p
  have hcq : c < u q := (hulower i).trans (U.toSurgeryWindows.lower_lt_value q)
  have hclass := equalFourCutSection_class husub hulevel (Γ i)
  have hpull : (equalFourCutHomologyEquiv hsub').symm (threeSectionClass (Δ i)) =
      (equalFourCutHomologyEquiv hsub).symm (threeSectionClass (Γ i)) := by
    rw [← equalFourCutHomologyEquiv_trans hsub husub]
    change (equalFourCutHomologyEquiv hsub).symm
      ((equalFourCutHomologyEquiv husub).symm (threeSectionClass (Δ i))) = _
    rw [← hclass, LinearEquiv.symm_apply_apply]
  have hunit : (L ((equalFourCutHomologyEquiv hsub').symm
      (threeSectionClass (Δ i)))).natAbs = 1 := by
    rw [hpull]
    rcases hi with hi | hi <;> rw [hi] <;> norm_num
  have hforward (y : (S.data p).UpperLevel) :
      Tendsto (fun t => U.flow t y.val) atTop (𝓝 p.val) ↔
        Tendsto (fun t => S.flow t y.val) atTop (𝓝 p.val) := by
    rw [huflow]
    exact (hkeep y.val y.property.le).2.2 p.val
  let _ := RegularLevel.chartedSpace hu hua
  obtain ⟨v, hv, hmv, hinjv, hcard, hcv, hvidx, hvgerm, hvstrict⟩ :=
    cancel_from_preserved_three_belt_unit S U hf hu hmu hdim p hindex hnull hpcrit hpnew
      q hq hconsecutive hqb hpc hcq hsub' hlevel' hua hforward (Δ i)
        (hfamily.1 i) (hfamily.2.1 i).injective (hfamily.2.2.1 i) (hfamily.2.2.2.2 i) hunit
  refine ⟨i, v, hv, hmv, hinjv, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [hcrit'] at hcard
  · simpa only [hcrit'] using hcv
  · intro z hz
    exact (hvidx z hz).trans (hids z (hcrit' ▸ ((hcv z).mp hz).1))
  · intro z hz
    have huz : b ≤ u z := le_of_not_gt (fun h => hz.not_gt ((hstrict' z).mp h))
    exact (hvgerm z huz).trans (hupper' z hz)
  · intro z
    exact (hvstrict z).trans (hstrict' z)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
