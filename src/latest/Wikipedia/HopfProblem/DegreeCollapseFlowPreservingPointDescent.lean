import Wikipedia.HopfProblem.DegreeCollapseFlowPreservingValueExchange
import Wikipedia.HopfProblem.DegreeCollapseFinitePointDescent

/-!
# Lower one critical value to its higher endpoint, retaining the same flow

Among excellent functions with the fixed critical set, indices, two endpoint
values and native field germs, minimize the rank of the chosen upper point.
An intervening critical point has an immediate predecessor below the upper
one. Its no-connection exchange lowers that rank and preserves all required
data. Thus the selected pair becomes consecutive without changing the flow.
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

theorem exists_flow_preserving_consecutive_pair
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
    (hnoconnection : ∀ j : criticalPoints E f₀, j ≠ q → j ≠ p → j ≠ r → ∀ x,
      ¬(Tendsto (fun t => F t x) atBot (𝓝 q.val) ∧
        Tendsto (fun t => F t x) atTop (𝓝 j.val))) :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f ∧
      criticalPoints E f = criticalPoints E f₀ ∧ InjOn f (criticalPoints E f) ∧
      f p = f₀ p ∧ f r = f₀ r ∧ f p < f q ∧
      (∀ z : criticalPoints E f₀, ¬(f p < f z ∧ f z < f q)) ∧
      (∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
      (∀ x ∈ criticalPoints E f, ∃ c : SignedMorseChart (E := E) f x,
        ∀ᶠ y in 𝓝 x, V y = c.descentField y) ∧
      ∀ x ∈ criticalPoints E f₀, nativeMorseIndex E f x = nativeMorseIndex E f₀ x := by
  classical
  let _ := (finite_criticalPoints hf₀ hm₀).fintype
  let P : ℕ → Prop := fun n => ∃ f : M → ℝ,
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f ∧
    criticalPoints E f = criticalPoints E f₀ ∧ InjOn f (criticalPoints E f) ∧
    f p = f₀ p ∧ f r = f₀ r ∧ f p < f q ∧
    (∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
    (∀ x ∈ criticalPoints E f, ∃ c : SignedMorseChart (E := E) f x,
      ∀ᶠ y in 𝓝 x, V y = c.descentField y) ∧
    (∀ x ∈ criticalPoints E f₀, nativeMorseIndex E f x = nativeMorseIndex E f₀ x) ∧
    beforeValueRank (fun x : criticalPoints E f₀ => f x) q = n
  have hex : ∃ n, P n := ⟨beforeValueRank (fun x : criticalPoints E f₀ => f₀ x) q,
    f₀, hf₀, hm₀, rfl, hinj₀, rfl, rfl, hpq, hdesc₀, hmodels₀, fun _ _ => rfl, rfl⟩
  obtain ⟨f, hf, hm, hcrit, hinj, hfp, hfr, hfpq, hdesc, hmodels, hindices, hrank⟩ :=
    Nat.find_spec hex
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
    obtain ⟨g, hg, hmg, hcritg, hinjg, hgz, hgq, hothers, hdescg, hmodelsg, hindicesg, -⟩ :=
      exists_flow_preserving_value_exchange hf hm hinj hV F hF
        (fun x hx => hzero x (hcrit ▸ hx)) hdesc hmodels zf qf hzq hbeforef
        (hnoconnection z (fun h => hzq' (congrArg Subtype.val h))
          (fun h => hzp (congrArg Subtype.val h)) (fun h => hzr (congrArg Subtype.val h)))
    have hpcrit : p.val ∈ criticalPoints E f := by rw [hcrit]; exact p.property
    have hrcrit : r.val ∈ criticalPoints E f := by rw [hcrit]; exact r.property
    have hpq' : p.val ≠ q.val := fun h => (ne_of_lt hfpq) (congrArg f h)
    have hrq' : r.val ≠ q.val := by
      intro h
      have hrp' : f r < f p := by rw [hfr, hfp]; exact hrp
      have hlt : f r < f q := hrp'.trans hfpq
      exact (ne_of_lt hlt) (congrArg f h)
    have hgp : g p = f p := (hothers p hpcrit hzp.symm hpq').self_of_nhds
    have hgr : g r = f r := (hothers r hrcrit hzr.symm hrq').self_of_nhds
    have hidxg₀ (x : M) (hx : x ∈ criticalPoints E f₀) :
        nativeMorseIndex E g x = nativeMorseIndex E f₀ x :=
      (hindicesg x (by rw [hcrit]; exact hx)).trans (hindices x hx)
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
        (by rw [hgp, hgq]; exact hpz), hdescg, hmodelsg, hidxg₀, rfl⟩
    rw [← hrank] at hminimal
    exact (not_le_of_gt hdecrease) hminimal
  exact ⟨f, hf, hm, hcrit, hinj, hfp, hfr, hfpq, hconsecutive, hdesc, hmodels, hindices⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
