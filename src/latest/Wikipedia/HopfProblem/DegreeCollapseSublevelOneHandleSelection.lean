import Wikipedia.HopfProblem.DegreeCollapseOrderedMinimumCount

/-!
# Select an actual merging one-handle below a fixed regular cut

Connectedness of the original sublevel, rather than of the whole closed
manifold, descends through its actual surgery windows. Two distinct
minima below the cut therefore force a component-merging one-handle
below that SAME cut. No condition is imposed on the handles above it.
-/

noncomputable section

open Set Function ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  {f : M → ℝ} (S : SurgeryWindows E f)

theorem ordered_upper_pathConnected_below_cut
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : ∀ x, f x = a → x ∉ criticalPoints E f)
    [PathConnectedSpace {x : M // f x ≤ a}]
    (hcut : ∀ p : criticalPoints E f, f p < a → S.upper p < a)
    (i : Fin S.count) (hi : f (S.point i) < a)
    (htransfer : ∀ j : Fin S.count, i < j → f (S.point j) < a →
      PathConnectedSpace {x : M // f x ≤ S.upper (S.point j)} →
        PathConnectedSpace {x : M // f x ≤ S.lower (S.point j)}) :
    PathConnectedSpace {x : M // f x ≤ S.upper (S.point i)} := by
  have hall : ∀ k : ℕ, ∀ i : Fin S.count, S.count - 1 - i.val = k →
      f (S.point i) < a →
      (∀ j : Fin S.count, i < j → f (S.point j) < a →
        PathConnectedSpace {x : M // f x ≤ S.upper (S.point j)} →
          PathConnectedSpace {x : M // f x ≤ S.lower (S.point j)}) →
      PathConnectedSpace {x : M // f x ≤ S.upper (S.point i)} := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hki hi htrans
      by_cases hlast : ∀ j : Fin S.count, i < j → ¬f (S.point j) < a
      · have hband (x : M) (hx : f x ∈ Icc (S.upper (S.point i)) a) :
            x ∉ criticalPoints E f := by
          intro hxc
          let p : criticalPoints E f := ⟨x, hxc⟩
          let j := S.point.symm p
          have hj : S.point j = p := S.point.apply_symm_apply p
          have hij : i < j := S.point_strictMono.lt_iff_lt.mp (by
            rw [hj]
            exact (S.value_lt_upper (S.point i)).trans_le hx.1)
          have hxa : f x < a := lt_of_le_of_ne hx.2 (fun h => ha x h hxc)
          exact hlast j hij (by simpa only [hj] using hxa)
        obtain ⟨e, _⟩ := FlowConstruction.exists_regularSublevelHomotopyEquiv
          hf (hcut (S.point i) hi).le hband
        exact pathConnectedSpace_of_homotopyEquiv e
      · push Not at hlast
        obtain ⟨j₀, hij₀, hj₀⟩ := hlast
        have hjlt : i.val + 1 < S.count := by have := j₀.isLt; omega
        let j : Fin S.count := ⟨i.val + 1, hjlt⟩
        have hij : i < j := by change i.val < i.val + 1; omega
        have hjj₀ : j ≤ j₀ := by change i.val + 1 ≤ j₀.val; exact hij₀
        have hj : f (S.point j) < a := (S.point_strictMono.monotone hjj₀).trans_lt hj₀
        have hmeasure : S.count - 1 - j.val < k := by dsimp [j]; omega
        have hupper := ih _ hmeasure j rfl hj
          (fun q hq hqa => htrans q (hij.trans hq) hqa)
        let : PathConnectedSpace {x : M // f x ≤ S.lower (S.point j)} :=
          htrans j hij hj hupper
        obtain ⟨e, _⟩ := FlowConstruction.exists_regularSublevelHomotopyEquiv hf
          (S.ordered_windows i j hij).le (S.consecutive_regular i j rfl)
        exact pathConnectedSpace_of_homotopyEquiv e
  exact hall _ i rfl hi htransfer

theorem exists_native_merging_one_handle_below_cut
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : ∀ x, f x = a → x ∉ criticalPoints E f)
    [PathConnectedSpace {x : M // f x ≤ a}]
    (hcut : ∀ p : criticalPoints E f, f p < a → S.upper p < a)
    (p₀ p₁ : criticalPoints E f) (hp₀ : f p₀ < a) (hp₁ : f p₁ < a)
    (hzero₀ : nativeMorseIndex E f p₀ = 0) (hzero₁ : nativeMorseIndex E f p₁ = 0)
    (hne : p₀ ≠ p₁) :
    ∃ q : criticalPoints E f, f q < a ∧ nativeMorseIndex E f q = 1 ∧
      ∃ u v, ¬Joined ((S.data q).coreBoundaryMap u) ((S.data q).coreBoundaryMap v) := by
  classical
  by_contra hnot
  let K : Finset (Fin S.count) :=
    Finset.univ.filter (fun i => f (S.point i) < a ∧ nativeMorseIndex E f (S.point i) = 0)
  have hp₀K : S.point.symm p₀ ∈ K := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by simpa using And.intro hp₀ hzero₀⟩
  have hK : K.Nonempty := ⟨_, hp₀K⟩
  let j : Fin S.count := K.max' hK
  obtain ⟨hjcut, hjzero⟩ := (Finset.mem_filter.mp (K.max'_mem hK)).2
  have hmax (i : Fin S.count) (hi : f (S.point i) < a)
      (hzero : nativeMorseIndex E f (S.point i) = 0) : i ≤ j :=
    K.le_max' i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, hzero⟩)
  have htail (i : Fin S.count) (hji : j < i) (hi : f (S.point i) < a)
      (hupper : PathConnectedSpace {x : M // f x ≤ S.upper (S.point i)}) :
      PathConnectedSpace {x : M // f x ≤ S.lower (S.point i)} := by
    let : PathConnectedSpace
        {x : M // f x ≤ f (S.point i) + (S.data (S.point i)).radius ^ 2} := hupper
    have hnezero : nativeMorseIndex E f (S.point i) ≠ 0 :=
      fun h => (not_le_of_gt hji) (hmax i hi h)
    have heq := nativeMorseIndex_eq_chart (S.data (S.point i)).chart
    by_cases hone : nativeMorseIndex E f (S.point i) = 1
    · have hjoined : ∀ u v,
          Joined ((S.data (S.point i)).coreBoundaryMap u)
            ((S.data (S.point i)).coreBoundaryMap v) := by
        intro u v
        by_contra huv
        exact hnot ⟨S.point i, hi, hone, u, v, huv⟩
      obtain ⟨z, hz⟩ := native_attaching_component_of_pairwise_joined
        (S.data (S.point i)) (by omega) hjoined
      exact native_lower_pathConnected_of_attaching_component (S.data (S.point i))
        hf.continuous z hz
    · exact native_lower_pathConnected_of_upper (S.data (S.point i)) hf.continuous (by omega)
  let : PathConnectedSpace
      {x : M // f x ≤ f (S.point j) + (S.data (S.point j)).radius ^ 2} :=
    ordered_upper_pathConnected_below_cut S hf ha hcut j hjcut htail
  let : IsEmpty {x : M // f x ≤ f (S.point j) - (S.data (S.point j)).radius ^ 2} :=
    native_zero_handle_lower_isEmpty (S.data (S.point j)) hf.continuous
      ((nativeMorseIndex_eq_chart (S.data (S.point j)).chart).symm.trans hjzero)
  have honly (p : criticalPoints E f) (hp : f p < a)
      (hz : nativeMorseIndex E f p = 0) : p = S.point j := by
    let i := S.point.symm p
    have hip : S.point i = p := S.point.apply_symm_apply p
    have hij : i ≤ j := hmax i (by simpa only [hip] using hp) (by simpa only [hip] using hz)
    rcases lt_or_eq_of_le hij with hlt | heq
    · have hbelow : f p ≤ S.lower (S.point j) := by
        rw [← hip]
        exact (S.value_lt_upper (S.point i)).le.trans (S.ordered_windows i j hlt).le
      exact isEmptyElim (⟨p.val, hbelow⟩ :
        {x : M // f x ≤ f (S.point j) - (S.data (S.point j)).radius ^ 2})
    · exact hip.symm.trans (congrArg S.point heq)
  exact hne ((honly p₀ hp₀ hzero₀).trans (honly p₁ hp₁ hzero₁).symm)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
