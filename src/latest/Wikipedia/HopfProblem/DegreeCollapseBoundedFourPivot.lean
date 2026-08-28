import Wikipedia.HopfProblem.DegreeCollapseBoundedFourFamilyExchange
import Wikipedia.HopfProblem.DegreeCollapseFinitePointDescent

/-!
# Move any four-handle pivot first inside the original two regular cuts

Minimize the finite number of labelled critical values below the selected
pivot. Completeness of the family in the open band makes its immediate
predecessor globally consecutive. The original full basin section excludes
a connecting orbit, so a bounded native value exchange lowers this rank.
Both outer germs, the complete field and flow, the exact source parameters,
and the actual matrix in the literally transported basis remain unchanged.
No ordering of critical indices outside the band is required.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse
open Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

local notation "S₃" => Hemisphere.Sphere 3

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

omit [T2Space M] [CompactSpace M] in
theorem nativeFourBasinFamily_labels_injective
    (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    {n : ℕ} (p : Fin n → criticalPoints E f)
    (γ : Fin n → C(S₃, {y : M // f y = a}))
    (hγ : IsNativeFourBasinFamily S hf ha p (fun j => γ j)) : Injective p := by
  intro i j hij
  by_contra hne
  let x : S₃ := Hemisphere.point true ⟨0, by simp⟩
  have hbasin := (hγ.2.2.2.2 i (γ i x)).mp (mem_range_self x)
  have hj : γ i x ∈ range (γ j) := by
    apply (hγ.2.2.2.2 j (γ i x)).mpr
    simpa only [hij] using hbasin
  exact Set.disjoint_left.mp (hγ.2.2.2.1 hne) (mem_range_self x) hj

variable [PreconnectedSpace M]

theorem AdaptedSurgeryWindows.exists_bounded_first_four_pivot
    (S₀ : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {a b : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    {r n : ℕ} (p : Fin n → criticalPoints E f)
    (hp : ∀ j, nativeMorseIndex E f (p j) = 4)
    (hvalues : ∀ j, a < f (p j) ∧ f (p j) < b)
    (hcomplete : ∀ z : criticalPoints E f, a < f z → f z < b → ∃ j, p j = z)
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ a} 3)
    (γ : Fin n → C(S₃, {y : M // f y = a}))
    (hγ : IsNativeFourBasinFamily S₀ hf ha p (fun j => γ j))
    (hsurj : Surjective (canonicalFourMatrix B γ).mulVec) (q : Fin n) :
    ∃ g : M → ℝ, ∃ hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g,
      IsMorse E g ∧ ∃ hcrit : criticalPoints E g = criticalPoints E f,
        InjOn g (criticalPoints E g) ∧
        (∀ z ∈ criticalPoints E f, nativeMorseIndex E g z = nativeMorseIndex E f z) ∧
        (∀ k, nativeMorseCount E g k = nativeMorseCount E f k) ∧
        (∀ z ∈ criticalPoints E f, (∀ j, z ≠ (p j).val) → g =ᶠ[𝓝 z] f) ∧
        (∀ j, j ≠ q → g (p q) < g (p j)) ∧
        ∃ hsub : ∀ y, g y ≤ a ↔ f y ≤ a,
        ∃ hlevel : ∀ y, g y = a ↔ f y = a,
        (∀ y, g y < b ↔ f y < b) ∧ (∀ y, g y = b ↔ f y = b) ∧
        (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧ (∀ y, b ≤ f y → g =ᶠ[𝓝 y] f) ∧
        ∃ hga : ∀ y, g y = a → y ∉ criticalPoints E g,
        ∃ _hgb : ∀ y, g y = b → y ∉ criticalPoints E g,
        ∃ W : AdaptedSurgeryWindows E g, W.field = S₀.field ∧ W.flow = S₀.flow ∧
          let p' : Fin n → criticalPoints E g :=
            fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
          let B' := B.trans (equalFourCutHomologyEquiv hsub)
          let γ' := fun j => equalFourCutSection hlevel (γ j)
          (∀ j, nativeMorseIndex E g (p' j) = 4) ∧
          (∀ z : criticalPoints E g, a < g z → g z < b → ∃ j, p' j = z) ∧
          (∀ j, a < W.toSurgeryWindows.lower (p' j)) ∧
          (∀ j, W.toSurgeryWindows.upper (p' j) < b) ∧
          IsNativeFourBasinFamily W hg hga p' (fun j => γ' j) ∧
          (∀ j x, (γ' j x).val = (γ j x).val) ∧
          canonicalFourMatrix B' γ' = canonicalFourMatrix B γ ∧
          Surjective (canonicalFourMatrix B' γ').mulVec := by
  classical
  have hpinj := nativeFourBasinFamily_labels_injective S₀ hf ha p γ hγ
  let P : ℕ → Prop := fun m => ∃ g : M → ℝ,
    ∃ hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g,
    IsMorse E g ∧ ∃ _hc : criticalPoints E g = criticalPoints E f,
    (∀ y, g y ≤ a ↔ f y ≤ a) ∧ (∀ y, g y = a ↔ f y = a) ∧
    (∀ y, g y < b ↔ f y < b) ∧ (∀ y, g y = b ↔ f y = b) ∧
    (∀ y, g y = a → y ∉ criticalPoints E g) ∧
    (∀ y, g y = b → y ∉ criticalPoints E g) ∧
    ∃ T : AdaptedSurgeryWindows E g,
      (∀ z ∈ criticalPoints E f, nativeMorseIndex E g z = nativeMorseIndex E f z) ∧
      (∀ z ∈ criticalPoints E f, (∀ j, z ≠ (p j).val) → g =ᶠ[𝓝 z] f) ∧
      T.field = S₀.field ∧ T.flow = S₀.flow ∧
      (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧ (∀ y, b ≤ f y → g =ᶠ[𝓝 y] f) ∧
      beforeValueRank (fun j => g (p j)) q = m
  have hex : ∃ m, P m := ⟨beforeValueRank (fun j => f (p j)) q,
    f, hf, hm, rfl, fun _ => Iff.rfl, fun _ => Iff.rfl,
    fun _ => Iff.rfl, fun _ => Iff.rfl, ha, hb, S₀,
    fun _ _ => rfl, fun _ _ _ => Filter.EventuallyEq.rfl, rfl, rfl,
    fun _ _ => Filter.EventuallyEq.rfl, fun _ _ => Filter.EventuallyEq.rfl, rfl⟩
  obtain ⟨g, hg, hmg, hcrit, hsub, hlevel, hstrict, hlevelB, hga, hgb,
    T, hindices, houtside, hfield, hflow, hlowgerm, huppergerm, hrank⟩ := Nat.find_spec hex
  let pg : Fin n → criticalPoints E g :=
    fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
  let Bg := B.trans (equalFourCutHomologyEquiv hsub)
  let γg := fun j => equalFourCutSection hlevel (γ j)
  have hpg (j : Fin n) : nativeMorseIndex E g (pg j) = 4 :=
    (hindices (p j) (p j).property).trans (hp j)
  have hfamily : IsNativeFourBasinFamily T hg hga pg (fun j => γg j) :=
    nativeFourBasinFamily_equalCut S₀ T hf hg ha hga hcrit hlevel hflow p γ hγ
  have hmatrix : canonicalFourMatrix Bg γg = canonicalFourMatrix B γ :=
    canonicalFourMatrix_equalCut hsub hlevel B γ
  have hgsurj : Surjective (canonicalFourMatrix Bg γg).mulVec := by
    rw [hmatrix]
    exact hsurj
  have hinside (j : Fin n) : a < g (pg j) ∧ g (pg j) < b := by
    refine ⟨lt_of_not_ge (fun h => (hvalues j).1.not_ge ((hsub (p j)).mp h)), ?_⟩
    exact (hstrict (p j)).mpr (hvalues j).2
  have hpgcomplete (z : criticalPoints E g) (haz : a < g z) (hzb : g z < b) :
      ∃ j, pg j = z := by
    let zf : criticalPoints E f := ⟨z.val, hcrit ▸ z.property⟩
    have haf : a < f zf :=
      lt_of_not_ge (fun h => haz.not_ge ((hsub z).mpr h))
    have hfb : f zf < b := (hstrict z).mp hzb
    obtain ⟨j, hj⟩ := hcomplete zf haf hfb
    exact ⟨j, Subtype.ext (congrArg (fun z : criticalPoints E f => z.val) hj)⟩
  have hvalueinj : Injective (fun j => g (p j)) := by
    intro i j hij
    exact hpinj (Subtype.ext (T.distinct (pg i).property (pg j).property hij))
  have hfirst : ∀ j, j ≠ q → g (p q) < g (p j) := by
    intro j hj
    by_contra hnot
    have hjq : g (p j) < g (p q) := lt_of_le_of_ne (le_of_not_gt hnot)
      (fun heq => hj (hvalueinj heq))
    let K := Finset.univ.filter (fun k => g (p k) < g (p q))
    have hjK : j ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjq⟩
    obtain ⟨i, hi, hmax⟩ := K.exists_max_image (fun k => g (p k)) ⟨j, hjK⟩
    have hiq : g (p i) < g (p q) := (Finset.mem_filter.mp hi).2
    have hconsecutive : ∀ k, ¬(g (p i) < g (p k) ∧ g (p k) < g (p q)) := by
      intro k hk
      exact (not_lt_of_ge (hmax k (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hk.2⟩))) hk.1
    have hglobal : ∀ z : criticalPoints E g, ¬(g (pg i) < g z ∧ g z < g (pg q)) := by
      intro z hz
      obtain ⟨k, hk⟩ := hpgcomplete z ((hinside i).1.trans hz.1)
        (hz.2.trans (hinside q).2)
      exact hconsecutive k (by simpa only [← hk] using hz)
    obtain ⟨u, hu, hmu, hcu, -, hui, huq, huothers, huindices, -, hus, hul,
      hustrict, hulevelB, hugermlow, hugermupper, hua, hub, U, hufield, huflow, _⟩ :=
      T.exists_bounded_four_family_value_exchange hg hmg hga hgb pg hpg hinside Bg γg
        hfamily hgsurj i q hiq hglobal
    have hdecrease : beforeValueRank (fun k => u (p k)) q <
        beforeValueRank (fun k => g (p k)) q := by
      apply beforeValueRank_exchange_lt hvalueinj hiq hconsecutive hui huq
      intro k hki hkq
      have hother := huothers (pg k) (pg k).property
        (fun heq => hki (hpinj (Subtype.ext heq)))
        (fun heq => hkq (hpinj (Subtype.ext heq)))
      exact hother.self_of_nhds
    have hupperu (y : M) (hy : b ≤ f y) : u =ᶠ[𝓝 y] f := by
      have hgy : b ≤ g y := le_of_not_gt (fun h => hy.not_gt ((hstrict y).mp h))
      exact (hugermupper y hgy).trans (huppergerm y hy)
    have hminimal := Nat.find_min' hex (show P (beforeValueRank (fun k => u (p k)) q) from
      ⟨u, hu, hmu, hcu.trans hcrit, fun y => (hus y).trans (hsub y),
        fun y => (hul y).trans (hlevel y), fun y => (hustrict y).trans (hstrict y),
        fun y => (hulevelB y).trans (hlevelB y), hua, hub, U,
        fun z hz => (huindices z (hcrit.symm ▸ hz)).trans (hindices z hz),
        fun z hz hzoutside =>
          (huothers z (hcrit.symm ▸ hz) (hzoutside i) (hzoutside q)).trans
            (houtside z hz hzoutside),
        hufield.trans hfield, huflow.trans hflow,
        fun y hy => (hugermlow y ((hsub y).mpr hy)).trans (hlowgerm y hy),
        hupperu, rfl⟩)
    rw [← hrank] at hminimal
    exact (not_le_of_gt hdecrease) hminimal
  obtain ⟨W, hWfield, hWflow, _, _, _, hWaboveA, hWbelowB, _⟩ :=
    T.exists_same_flow_windows_avoiding_two_levels hg hmg hga hgb
  refine ⟨g, hg, hmg, hcrit, T.distinct, hindices,
    nativeMorseCount_eq_of_preserved_indices hcrit hindices, houtside, hfirst,
    hsub, hlevel, hstrict, hlevelB, hlowgerm, huppergerm, hga, hgb,
    W, hWfield.trans hfield, hWflow.trans hflow, hpg, hpgcomplete,
    fun j => hWaboveA (pg j) (hinside j).1, fun j => hWbelowB (pg j) (hinside j).2,
    ?_, fun _ _ => rfl, hmatrix, hgsurj⟩
  exact nativeFourBasinFamily_equalCut S₀ W hf hg ha hga hcrit hlevel
    (hWflow.trans hflow) p γ hγ

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
