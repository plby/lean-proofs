import Wikipedia.HopfProblem.DegreeCollapsePositiveFlowPointDescent

/-!
# Relative value descent needs only positive connection exclusion

Move the upper point down to the selected positive lower point using the
same actual complete flow. Only positive predecessors are exchanged.
Every excellent presentation of the same state has the same positive
subset, so the original positive connection exclusion still applies after
each exchange. Arbitrary negative endpoint connections are allowed.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization
open Wikipedia.SmoothSixDPoincare ManifoldMorse
open MorseCancellation MorseRearrangement

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

theorem exists_consecutive_pair_of_no_other_positive_connection
    {V : (x : S.Space) → TangentSpace (𝓡 7) x}
    (hV : ContMDiff (𝓡 7) (𝓡 7).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle (𝓡 7) S.Space)))
    (F : Flow ℝ S.Space) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ criticalPoints (Vector 7) P.function, V x = 0)
    (hdesc₀ : ∀ x, x ∉ criticalPoints (Vector 7) P.function →
      mvfderiv (𝓡 7) P.function x (V x) < 0)
    (hmodels₀ : ∀ x ∈ criticalPoints (Vector 7) P.function,
      ∃ c : SignedMorseChart (E := Vector 7) P.function x,
        ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (p q : criticalPoints (Vector 7) P.function)
    (hpositive : 0 < P.function p) (hpq : P.function p < P.function q)
    (hnoconnection : ∀ j : criticalPoints (Vector 7) P.function,
      0 < P.function j → j ≠ q → j ≠ p → ∀ x,
        ¬(Tendsto (fun t => F t x) atBot (𝓝 q.val) ∧
          Tendsto (fun t => F t x) atTop (𝓝 j.val))) :
    ∃ Q : S.ExcellentMorsePresentation,
      criticalPoints (Vector 7) Q.function = criticalPoints (Vector 7) P.function ∧
      Q.function p = P.function p ∧ Q.function p < Q.function q ∧
      (∀ z : criticalPoints (Vector 7) P.function,
        ¬(Q.function p < Q.function z ∧ Q.function z < Q.function q)) ∧
      (∀ x, x ∉ criticalPoints (Vector 7) Q.function →
        mvfderiv (𝓡 7) Q.function x (V x) < 0) ∧
      (∀ x ∈ criticalPoints (Vector 7) Q.function,
        ∃ c : SignedMorseChart (E := Vector 7) Q.function x,
          ∀ᶠ y in 𝓝 x, V y = c.descentField y) ∧
      (∀ x ∈ criticalPoints (Vector 7) P.function,
        nativeMorseIndex (Vector 7) Q.function x = nativeMorseIndex (Vector 7) P.function x) ∧
      ∀ x, S.time x ≤ 0 → Q.function =ᶠ[𝓝 x] P.function := by
  classical
  let : Fintype (criticalPoints (Vector 7) P.function) := P.finite_criticalPoints.fintype
  let C : ℕ → Prop := fun n => ∃ Q : S.ExcellentMorsePresentation,
    criticalPoints (Vector 7) Q.function = criticalPoints (Vector 7) P.function ∧
    Q.function p = P.function p ∧ Q.function p < Q.function q ∧
    (∀ x, x ∉ criticalPoints (Vector 7) Q.function →
      mvfderiv (𝓡 7) Q.function x (V x) < 0) ∧
    (∀ x ∈ criticalPoints (Vector 7) Q.function,
      ∃ c : SignedMorseChart (E := Vector 7) Q.function x,
        ∀ᶠ y in 𝓝 x, V y = c.descentField y) ∧
    (∀ x ∈ criticalPoints (Vector 7) P.function,
      nativeMorseIndex (Vector 7) Q.function x = nativeMorseIndex (Vector 7) P.function x) ∧
    (∀ x, S.time x ≤ 0 → Q.function =ᶠ[𝓝 x] P.function) ∧
    beforeValueRank (fun x : criticalPoints (Vector 7) P.function => Q.function x) q = n
  have hex : ∃ n, C n :=
    ⟨beforeValueRank (fun x : criticalPoints (Vector 7) P.function => P.function x) q,
      P, rfl, rfl, hpq, hdesc₀, hmodels₀, fun _ _ => rfl,
      fun _ _ => Filter.EventuallyEq.rfl, rfl⟩
  obtain ⟨Q, hcrit, hQp, hQpq, hdesc, hmodels, hindices, hnegative, hrank⟩ := Nat.find_spec hex
  have hconsecutive : ∀ z : criticalPoints (Vector 7) P.function,
      ¬(Q.function p < Q.function z ∧ Q.function z < Q.function q) := by
    by_contra hnot
    push Not at hnot
    obtain ⟨z, hpz, hzq, hbefore⟩ := exists_consecutive_below_of_intermediate
      (h := fun x : criticalPoints (Vector 7) P.function => Q.function x) (p := p) (q := q) hnot
    have hzp : z.val ≠ p.val := fun h => (ne_of_lt hpz) (congrArg Q.function h).symm
    have hzq' : z.val ≠ q.val := fun h => (ne_of_lt hzq) (congrArg Q.function h)
    let zQ : criticalPoints (Vector 7) Q.function := ⟨z.val, hcrit.symm ▸ z.property⟩
    let qQ : criticalPoints (Vector 7) Q.function := ⟨q.val, hcrit.symm ▸ q.property⟩
    have hbeforeQ : ∀ s : criticalPoints (Vector 7) Q.function,
        ¬(Q.function zQ < Q.function s ∧ Q.function s < Q.function qQ) := by
      intro s hs
      exact hbefore ⟨s.val, hcrit ▸ s.property⟩ hs
    have hzpositive : 0 < Q.function zQ :=
      (show 0 < Q.function p by rw [hQp]; exact hpositive).trans hpz
    have hzpositiveP : 0 < P.function z :=
      (P.positive_iff z).mpr ((Q.positive_iff z).mp hzpositive)
    obtain ⟨R, hcritR, hRz, hRq, hnegativeR, hothers, hdescR, hmodelsR, hindicesR, _⟩ :=
      Q.exists_positive_flow_preserving_exchange hV F hF
        (fun x hx => hzero x (hcrit ▸ hx)) hdesc hmodels zQ qQ hzpositive hzq hbeforeQ
        (hnoconnection z hzpositiveP (fun h => hzq' (congrArg Subtype.val h))
          (fun h => hzp (congrArg Subtype.val h)))
    have hpcrit : p.val ∈ criticalPoints (Vector 7) Q.function := hcrit.symm ▸ p.property
    have hpq' : p.val ≠ q.val := fun h => (ne_of_lt hQpq) (congrArg Q.function h)
    have hRp : R.function p = Q.function p := (hothers p hpcrit hzp.symm hpq').self_of_nhds
    have hRindices (x : S.Space) (hx : x ∈ criticalPoints (Vector 7) P.function) :
        nativeMorseIndex (Vector 7) R.function x = nativeMorseIndex (Vector 7) P.function x :=
      (hindicesR x (hcrit.symm ▸ hx)).trans (hindices x hx)
    have hdecrease :
        beforeValueRank (fun x : criticalPoints (Vector 7) P.function => R.function x) q <
          beforeValueRank (fun x : criticalPoints (Vector 7) P.function => Q.function x) q := by
      apply beforeValueRank_exchange_lt
        (h := fun x : criticalPoints (Vector 7) P.function => Q.function x)
        (g := fun x : criticalPoints (Vector 7) P.function => R.function x) (p := z) (q := q)
        (fun x y h => Subtype.ext (Q.distinct (hcrit.symm ▸ x.property)
          (hcrit.symm ▸ y.property) h)) hzq hbefore hRz hRq
      intro x hxz hxq
      exact (hothers x (hcrit.symm ▸ x.property)
        (fun h => hxz (Subtype.ext h)) (fun h => hxq (Subtype.ext h))).self_of_nhds
    have hminimal := Nat.find_min' hex
      ⟨R, hcritR.trans hcrit, hRp.trans hQp, (by rw [hRp, hRq]; exact hpz),
        hdescR, hmodelsR, hRindices,
        (fun x hx => (hnegativeR x hx).trans (hnegative x hx)), rfl⟩
    rw [← hrank] at hminimal
    exact (not_le_of_gt hdecrease) hminimal
  exact ⟨Q, hcrit, hQp, hQpq, hconsecutive, hdesc, hmodels, hindices, hnegative⟩

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
