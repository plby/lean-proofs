import Wikipedia.HopfProblem.DegreeCollapseMiddleFamilyValueExchange
import Wikipedia.HopfProblem.DegreeCollapseFinitePointDescent

/-!
# Move any represented middle pivot first by actual critical-value exchanges

Minimize the number of labelled values below the selected point among
actual native presentations with the same common cut and complete flow.
Any predecessor is globally consecutive, since index ordering and
completeness put every intervening critical point in the middle family.
The native exchange strictly lowers the finite rank. All parameter maps
and the geometric matrix survive by literal common-cut identification.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse
open Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem nativeMiddleBasinFamily_labels_injective
    (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    {n : ℕ} (p : Fin n → criticalPoints E f)
    (γ : Fin n → C(S₂, {y : M // f y = a}))
    (hγ : IsNativeMiddleBasinFamily S hf ha p (fun j => γ j)) : Injective p := by
  intro i j hij
  by_contra hne
  let x : S₂ := Hemisphere.point true ⟨0, by simp⟩
  have hbasin := (hγ.2.2.2.2 i (γ i x)).mp (mem_range_self x)
  have hj : γ i x ∈ range (γ j) := by
    apply (hγ.2.2.2.2 j (γ i x)).mpr
    simpa only [hij] using hbasin
  exact Set.disjoint_left.mp (hγ.2.2.2.1 hne) (mem_range_self x) hj

variable [PreconnectedSpace M] [Nonempty M]

theorem AdaptedSurgeryWindows.exists_first_middle_pivot
    (S₀ : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (horder : ∀ x y : criticalPoints E f, f x < f y →
      nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    {r n : ℕ} (p : Fin n → criticalPoints E f)
    (hp : ∀ j, nativeMorseIndex E f (p j) = 3)
    (hcomplete : ∀ z : criticalPoints E f, nativeMorseIndex E f z = 3 → ∃ j, p j = z)
    (hlower : ∀ j, a < S₀.toSurgeryWindows.lower (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ a} 2)
    (γ : Fin n → C(S₂, {y : M // f y = a}))
    (hγ : IsNativeMiddleBasinFamily S₀ hf ha p (fun j => γ j))
    (hsurj : Surjective (canonicalMiddleMatrix B γ).mulVec) (q : Fin n) :
    ∃ g : M → ℝ, ∃ hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g,
      IsMorse E g ∧ ∃ hcrit : criticalPoints E g = criticalPoints E f,
        (∀ x y : criticalPoints E g, g x < g y →
          nativeMorseIndex E g x ≤ nativeMorseIndex E g y) ∧
        (∀ z ∈ criticalPoints E f, nativeMorseIndex E g z = nativeMorseIndex E f z) ∧
        (∀ k, nativeMorseCount E g k = nativeMorseCount E f k) ∧
        (∀ z ∈ criticalPoints E f, (∀ j, z ≠ (p j).val) → g z = f z) ∧
        (∀ j, j ≠ q → g (p q) < g (p j)) ∧
        ∃ hsub : ∀ y, g y ≤ a ↔ f y ≤ a,
        ∃ hlevel : ∀ y, g y = a ↔ f y = a,
        ∃ hga : ∀ y, g y = a → y ∉ criticalPoints E g,
        ∃ T : AdaptedSurgeryWindows E g,
          T.field = S₀.field ∧ T.flow = S₀.flow ∧
          (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧
          let p' : Fin n → criticalPoints E g :=
            fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
          let B' := B.trans (equalCutHomologyEquiv hsub)
          let γ' := fun j => equalCutSection hlevel (γ j)
          (∀ j, nativeMorseIndex E g (p' j) = 3) ∧
          (∀ j, a < T.toSurgeryWindows.lower (p' j)) ∧
          IsNativeMiddleBasinFamily T hg hga p' (fun j => γ' j) ∧
          (∀ j x, (γ' j x).val = (γ j x).val) ∧
          canonicalMiddleMatrix B' γ' = canonicalMiddleMatrix B γ ∧
          Surjective (canonicalMiddleMatrix B' γ').mulVec := by
  classical
  have hpinj := nativeMiddleBasinFamily_labels_injective S₀ hf ha p γ hγ
  let P : ℕ → Prop := fun m => ∃ g : M → ℝ,
    ∃ hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g,
    IsMorse E g ∧ ∃ hc : criticalPoints E g = criticalPoints E f,
    ∃ hs : ∀ y, g y ≤ a ↔ f y ≤ a,
    ∃ hl : ∀ y, g y = a ↔ f y = a,
    ∃ hga : ∀ y, g y = a → y ∉ criticalPoints E g,
    ∃ T : AdaptedSurgeryWindows E g,
      (∀ x y : criticalPoints E g, g x < g y →
        nativeMorseIndex E g x ≤ nativeMorseIndex E g y) ∧
      (∀ z ∈ criticalPoints E f, nativeMorseIndex E g z = nativeMorseIndex E f z) ∧
      (∀ z ∈ criticalPoints E f, (∀ j, z ≠ (p j).val) → g z = f z) ∧
      T.field = S₀.field ∧ T.flow = S₀.flow ∧
      (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧
      (∀ j, a < T.toSurgeryWindows.lower ⟨(p j).val, hc.symm ▸ (p j).property⟩) ∧
      beforeValueRank (fun j => g (p j)) q = m
  have hex : ∃ m, P m := ⟨beforeValueRank (fun j => f (p j)) q,
    f, hf, hm, rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, ha, S₀,
    horder, fun _ _ => rfl, fun _ _ _ => rfl, rfl, rfl,
    fun _ _ => Filter.EventuallyEq.rfl, hlower, rfl⟩
  obtain ⟨g, hg, hmg, hcrit, hsub, hlevel, hga, T, hgorder, hindices,
    houtside, hfield, hflow, hgerm, hglower, hrank⟩ := Nat.find_spec hex
  let pg : Fin n → criticalPoints E g :=
    fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
  let Bg := B.trans (equalCutHomologyEquiv hsub)
  let γg := fun j => equalCutSection hlevel (γ j)
  have hpg (j : Fin n) : nativeMorseIndex E g (pg j) = 3 :=
    (hindices (p j) (p j).property).trans (hp j)
  have hfamily : IsNativeMiddleBasinFamily T hg hga pg (fun j => γg j) :=
    nativeMiddleBasinFamily_equalCut S₀ T hf hg ha hga hcrit hlevel hflow p γ hγ
  have hmatrix : canonicalMiddleMatrix Bg γg = canonicalMiddleMatrix B γ :=
    canonicalMiddleMatrix_equalCut hsub hlevel B γ
  have hgsurj : Surjective (canonicalMiddleMatrix Bg γg).mulVec := by
    rw [hmatrix]
    exact hsurj
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
      have hidx : nativeMorseIndex E g z = 3 := by
        apply Nat.le_antisymm
        · exact (hgorder z (pg q) hz.2).trans_eq (hpg q)
        · exact (hpg i).symm.trans_le (hgorder (pg i) z hz.1)
      let zf : criticalPoints E f := ⟨z.val, hcrit ▸ z.property⟩
      have hzf : nativeMorseIndex E f zf = 3 :=
        (hindices z zf.property).symm.trans hidx
      obtain ⟨k, hk⟩ := hcomplete zf hzf
      exact hconsecutive k (by simpa only [hk] using hz)
    obtain ⟨u, hu, hmu, hcu, -, hui, huq, huothers, huorder, huindices, -, hus, hul,
      hua, U, hufield, huflow, hugerm, -, hulower, -, -, -, -⟩ :=
      T.exists_middle_family_value_exchange hg hmg hga hgorder pg hpg hglower Bg γg
        hfamily hgsurj i q hiq hglobal
    have hdecrease : beforeValueRank (fun k => u (p k)) q <
        beforeValueRank (fun k => g (p k)) q := by
      apply beforeValueRank_exchange_lt hvalueinj hiq hconsecutive hui huq
      intro k hki hkq
      apply huothers (pg k) (pg k).property
      · exact fun heq => hki (hpinj (Subtype.ext heq))
      · exact fun heq => hkq (hpinj (Subtype.ext heq))
    have hminimal := Nat.find_min' hex (show P (beforeValueRank (fun k => u (p k)) q) from
      ⟨u, hu, hmu, hcu.trans hcrit, fun y => (hus y).trans (hsub y),
        fun y => (hul y).trans (hlevel y), hua, U, huorder,
        fun z hz => (huindices z (hcrit.symm ▸ hz)).trans (hindices z hz),
        fun z hz hzoutside =>
          (huothers z (hcrit.symm ▸ hz) (hzoutside i) (hzoutside q)).trans
            (houtside z hz hzoutside),
        hufield.trans hfield, huflow.trans hflow,
        fun y hy => (hugerm y ((hsub y).mpr hy)).trans (hgerm y hy), hulower, rfl⟩)
    rw [← hrank] at hminimal
    exact (not_le_of_gt hdecrease) hminimal
  exact ⟨g, hg, hmg, hcrit, hgorder, hindices,
    nativeMorseCount_eq_of_preserved_indices hcrit hindices, houtside, hfirst,
    hsub, hlevel, hga, T, hfield, hflow, hgerm, hpg, hglower, hfamily,
    fun _ _ => rfl, hmatrix, hgsurj⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
