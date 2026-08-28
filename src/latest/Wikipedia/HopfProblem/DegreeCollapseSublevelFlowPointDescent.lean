import Wikipedia.HopfProblem.DegreeCollapseSublevelFlowValueExchange
import Wikipedia.HopfProblem.DegreeCollapseFinitePointDescent

/-!
# Make a pair consecutive below the original cut, with the same flow

Minimize the actual upper-point rank while retaining both endpoint values,
the fixed complete flow and critical models, and the entire original upper
germ. Each exchange remains below the cut. Its literal strict sublevel is
also retained through the whole descent.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse
open Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M] {f₀ : M → ℝ}

theorem exists_flow_preserving_consecutive_pair_below_cut
    (hf₀ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f₀) (hm₀ : IsMorse E f₀)
    (hinj₀ : InjOn f₀ (criticalPoints E f₀))
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ criticalPoints E f₀, V x = 0)
    (hdesc₀ : ∀ x, x ∉ criticalPoints E f₀ → mvfderiv 𝓘(ℝ, E) f₀ x (V x) < 0)
    (hmodels₀ : ∀ x ∈ criticalPoints E f₀, ∃ c : SignedMorseChart (E := E) f₀ x,
      ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (p r q : criticalPoints E f₀) (hrp : f₀ r < f₀ p) (hpq : f₀ p < f₀ q)
    {a : ℝ} (hqa : f₀ q < a)
    (hnoconnection : ∀ j : criticalPoints E f₀, j ≠ q → j ≠ p → j ≠ r → ∀ x,
      ¬(Tendsto (fun t => F t x) atBot (𝓝 q.val) ∧
        Tendsto (fun t => F t x) atTop (𝓝 j.val))) :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f ∧
      criticalPoints E f = criticalPoints E f₀ ∧ InjOn f (criticalPoints E f) ∧
      f p = f₀ p ∧ f r = f₀ r ∧ f p < f q ∧ f q < a ∧
      (∀ z : criticalPoints E f₀, ¬(f p < f z ∧ f z < f q)) ∧
      (∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
      (∀ x ∈ criticalPoints E f, ∃ c : SignedMorseChart (E := E) f x,
        ∀ᶠ y in 𝓝 x, V y = c.descentField y) ∧
      (∀ x ∈ criticalPoints E f₀, nativeMorseIndex E f x = nativeMorseIndex E f₀ x) ∧
      (∀ x, a ≤ f₀ x → f =ᶠ[𝓝 x] f₀) ∧ ∀ x, f x < a ↔ f₀ x < a := by
  classical
  let _ := (finite_criticalPoints hf₀ hm₀).fintype
  let P : ℕ → Prop := fun n => ∃ f : M → ℝ,
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f ∧
    criticalPoints E f = criticalPoints E f₀ ∧ InjOn f (criticalPoints E f) ∧
    f p = f₀ p ∧ f r = f₀ r ∧ f p < f q ∧ f q < a ∧
    (∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
    (∀ x ∈ criticalPoints E f, ∃ c : SignedMorseChart (E := E) f x,
      ∀ᶠ y in 𝓝 x, V y = c.descentField y) ∧
    (∀ x ∈ criticalPoints E f₀, nativeMorseIndex E f x = nativeMorseIndex E f₀ x) ∧
    (∀ x, a ≤ f₀ x → f =ᶠ[𝓝 x] f₀) ∧ (∀ x, f x < a ↔ f₀ x < a) ∧
    beforeValueRank (fun x : criticalPoints E f₀ => f x) q = n
  have hex : ∃ n, P n := ⟨beforeValueRank (fun x : criticalPoints E f₀ => f₀ x) q,
    f₀, hf₀, hm₀, rfl, hinj₀, rfl, rfl, hpq, hqa, hdesc₀, hmodels₀,
    (fun _ _ => rfl), (fun _ _ => Filter.EventuallyEq.rfl), (fun _ => Iff.rfl), rfl⟩
  obtain ⟨f, hf, hm, hcrit, hinj, hfp, hfr, hfpq, hfqa, hdesc, hmodels,
      hindices, hkeep, hcut, hrank⟩ := Nat.find_spec hex
  have hconsecutive : ∀ z : criticalPoints E f₀, ¬(f p < f z ∧ f z < f q) := by
    by_contra hnot
    push Not at hnot
    obtain ⟨z, hpz, hzq, hbefore⟩ := exists_consecutive_below_of_intermediate
      (h := fun x : criticalPoints E f₀ => f x) (p := p) (q := q) hnot
    have hzp : z.val ≠ p.val := fun h => (ne_of_lt hpz) (congrArg f h).symm
    have hzq' : z.val ≠ q.val := fun h => (ne_of_lt hzq) (congrArg f h)
    have hzr : z.val ≠ r.val := by
      intro h
      have hrp' : f r < f p := by rw [hfr, hfp]; exact hrp
      exact (not_lt_of_gt hpz) (by simpa only [h] using hrp')
    let zf : criticalPoints E f := ⟨z.val, by rw [hcrit]; exact z.property⟩
    let qf : criticalPoints E f := ⟨q.val, by rw [hcrit]; exact q.property⟩
    have hbeforef : ∀ s : criticalPoints E f, ¬(f zf < f s ∧ f s < f qf) := by
      intro s hs
      exact hbefore ⟨s.val, by rw [← hcrit]; exact s.property⟩ hs
    obtain ⟨g, hg, hmg, hcritg, hinjg, hgz, hgq, hothers, hdescg, hmodelsg,
        hindicesg, _, hkeepg, hcutg⟩ := exists_flow_preserving_value_exchange_below_cut
      hf hm hinj hV F hF (fun x hx => hzero x (hcrit ▸ hx)) hdesc hmodels
        zf qf hzq hfqa hbeforef
        (hnoconnection z (fun h => hzq' (congrArg Subtype.val h))
          (fun h => hzp (congrArg Subtype.val h)) (fun h => hzr (congrArg Subtype.val h)))
    have hpcrit : p.val ∈ criticalPoints E f := by rw [hcrit]; exact p.property
    have hrcrit : r.val ∈ criticalPoints E f := by rw [hcrit]; exact r.property
    have hpq' : p.val ≠ q.val := fun h => (ne_of_lt hfpq) (congrArg f h)
    have hrq' : r.val ≠ q.val := by
      intro h
      have hrp' : f r < f p := by rw [hfr, hfp]; exact hrp
      exact (ne_of_lt (hrp'.trans hfpq)) (congrArg f h)
    have hgp : g p = f p := (hothers p hpcrit hzp.symm hpq').self_of_nhds
    have hgr : g r = f r := (hothers r hrcrit hzr.symm hrq').self_of_nhds
    have hidxg₀ (x : M) (hx : x ∈ criticalPoints E f₀) :
        nativeMorseIndex E g x = nativeMorseIndex E f₀ x :=
      (hindicesg x (by rw [hcrit]; exact hx)).trans (hindices x hx)
    have hkeepg₀ (x : M) (hx : a ≤ f₀ x) : g =ᶠ[𝓝 x] f₀ :=
      (hkeepg x (by rw [(hkeep x hx).self_of_nhds]; exact hx)).trans (hkeep x hx)
    have hdecrease : beforeValueRank (fun x : criticalPoints E f₀ => g x) q <
        beforeValueRank (fun x : criticalPoints E f₀ => f x) q := by
      apply beforeValueRank_exchange_lt
        (h := fun x : criticalPoints E f₀ => f x)
        (g := fun x : criticalPoints E f₀ => g x)
        (p := z) (q := q)
        (fun x y h => Subtype.ext (hinj (by rw [hcrit]; exact x.property)
          (by rw [hcrit]; exact y.property) h)) hzq hbefore hgz hgq
      intro x hxz hxq
      exact (hothers x (by rw [hcrit]; exact x.property)
        (fun h => hxz (Subtype.ext h)) (fun h => hxq (Subtype.ext h))).self_of_nhds
    have hminimal := Nat.find_min' hex
      ⟨g, hg, hmg, hcritg.trans hcrit, hinjg, hgp.trans hfp, hgr.trans hfr,
        (by rw [hgp, hgq]; exact hpz), (by rw [hgq]; exact hzq.trans hfqa),
        hdescg, hmodelsg, hidxg₀, hkeepg₀, (fun x => (hcutg x).trans (hcut x)), rfl⟩
    rw [← hrank] at hminimal
    exact (not_le_of_gt hdecrease) hminimal
  exact ⟨f, hf, hm, hcrit, hinj, hfp, hfr, hfpq, hfqa, hconsecutive,
    hdesc, hmodels, hindices, hkeep, hcut⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
