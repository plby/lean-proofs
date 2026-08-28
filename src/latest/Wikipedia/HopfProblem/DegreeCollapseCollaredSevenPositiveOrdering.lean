import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenPositiveExchange

/-!
# Native positive Morse ordering in the same original seven-dimensional state

Minimize the proved finite native disorder among excellent presentations
with the original critical set and indices and the same entire germ on
the nonpositive half. A positive inversion contains a consecutive positive
inversion, even among the full original critical set. Its actual positive
exchange stays in this class and strictly decreases disorder. Thus the
positive critical points become index ordered without changing the state
or its original boundary, and without an ordering assumption.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere GLOrthonormalization
open Wikipedia.SmoothSixDPoincare ManifoldMorse
open MorseCancellation MorseRearrangement

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}

namespace ExcellentMorsePresentation

variable (P : S.ExcellentMorsePresentation)

theorem exists_positive_adjacent_inversion
    (hnot : ¬∀ p q : criticalPoints (Vector 7) P.function,
      0 < P.function p → P.function p < P.function q →
        nativeMorseIndex (Vector 7) P.function p ≤ nativeMorseIndex (Vector 7) P.function q) :
    ∃ p q : criticalPoints (Vector 7) P.function,
      0 < P.function p ∧ P.function p < P.function q ∧
      (∀ r : criticalPoints (Vector 7) P.function,
        ¬(P.function p < P.function r ∧ P.function r < P.function q)) ∧
      nativeMorseIndex (Vector 7) P.function q < nativeMorseIndex (Vector 7) P.function p := by
  classical
  let K : Set S.Space := criticalPoints (Vector 7) P.function ∩ {x | 0 < P.function x}
  have hK : K.Finite := P.finite_criticalPoints.subset inter_subset_left
  let : Fintype K := hK.fintype
  have hi : Injective (fun x : K => P.function x.val) :=
    fun x y h => Subtype.ext (P.distinct x.property.1 y.property.1 h)
  have hnotK : ¬∀ x y : K, P.function x.val < P.function y.val →
      nativeMorseIndex (Vector 7) P.function x.val ≤
        nativeMorseIndex (Vector 7) P.function y.val := by
    intro h
    apply hnot
    intro p q hp hpq
    exact h ⟨p.val, p.property, hp⟩ ⟨q.val, q.property, hp.trans hpq⟩ hpq
  obtain ⟨p, q, hpq, hconsecutive, hindex⟩ := exists_adjacent_index_inversion hi
    (fun x : K => nativeMorseIndex (Vector 7) P.function x.val) hnotK
  refine ⟨⟨p.val, p.property.1⟩, ⟨q.val, q.property.1⟩, p.property.2, hpq, ?_, hindex⟩
  intro r hr
  exact hconsecutive ⟨r.val, r.property, p.property.2.trans hr.1⟩ hr

theorem exists_positive_index_ordered :
    ∃ Q : S.ExcellentMorsePresentation,
      criticalPoints (Vector 7) Q.function = criticalPoints (Vector 7) P.function ∧
      (∀ x ∈ criticalPoints (Vector 7) P.function,
        nativeMorseIndex (Vector 7) Q.function x = nativeMorseIndex (Vector 7) P.function x) ∧
      (∀ x, S.time x ≤ 0 → Q.function =ᶠ[𝓝 x] P.function) ∧
      (∀ p q : criticalPoints (Vector 7) Q.function,
        0 < Q.function p → Q.function p < Q.function q →
          nativeMorseIndex (Vector 7) Q.function p ≤ nativeMorseIndex (Vector 7) Q.function q) ∧
      ∀ k, nativeMorseCount (Vector 7) Q.function k = nativeMorseCount (Vector 7) P.function k := by
  classical
  let C : ℕ → Prop := fun n => ∃ Q : S.ExcellentMorsePresentation,
    criticalPoints (Vector 7) Q.function = criticalPoints (Vector 7) P.function ∧
    (∀ x ∈ criticalPoints (Vector 7) P.function,
      nativeMorseIndex (Vector 7) Q.function x = nativeMorseIndex (Vector 7) P.function x) ∧
    (∀ x, S.time x ≤ 0 → Q.function =ᶠ[𝓝 x] P.function) ∧
    nativeIndexDisorder (Vector 7) Q.function = n
  have hex : ∃ n, C n := ⟨nativeIndexDisorder (Vector 7) P.function,
    P, rfl, fun _ _ => rfl, fun _ _ => Filter.EventuallyEq.rfl, rfl⟩
  obtain ⟨Q, hcrit, hindices, hnegative, hdisorder⟩ := Nat.find_spec hex
  have horder : ∀ p q : criticalPoints (Vector 7) Q.function,
      0 < Q.function p → Q.function p < Q.function q →
        nativeMorseIndex (Vector 7) Q.function p ≤ nativeMorseIndex (Vector 7) Q.function q := by
    by_contra hnot
    obtain ⟨p, q, hpositive, hpq, hconsecutive, hinversion⟩ :=
      Q.exists_positive_adjacent_inversion hnot
    obtain ⟨R, hcritR, hRp, hRq, hnegativeR, hothers, hindicesR, _⟩ :=
      Q.exists_positive_index_exchange p q hpositive hpq hconsecutive hinversion.le
    have hdecrease : nativeIndexDisorder (Vector 7) R.function <
        nativeIndexDisorder (Vector 7) Q.function :=
      nativeIndexDisorder_exchange_lt Q.finite_criticalPoints Q.distinct
        p q hpq hconsecutive hinversion hcritR hRp hRq hothers hindicesR
    have hRindices (x : S.Space) (hx : x ∈ criticalPoints (Vector 7) P.function) :
        nativeMorseIndex (Vector 7) R.function x = nativeMorseIndex (Vector 7) P.function x :=
      (hindicesR x (hcrit.symm ▸ hx)).trans (hindices x hx)
    have hRnegative (x : S.Space) (hx : S.time x ≤ 0) : R.function =ᶠ[𝓝 x] P.function :=
      (hnegativeR x hx).trans (hnegative x hx)
    have hminimal := Nat.find_min' hex
      ⟨R, hcritR.trans hcrit, hRindices, hRnegative, rfl⟩
    rw [← hdisorder] at hminimal
    exact (not_le_of_gt hdecrease) hminimal
  exact ⟨Q, hcrit, hindices, hnegative, horder,
    nativeMorseCount_eq_of_preserved_indices hcrit hindices⟩

end ExcellentMorsePresentation

theorem exists_minimal_positive_index_ordered_presentation (S : CollaredSevenState B) :
    ∃ P : S.ExcellentMorsePresentation,
      (∀ p q : criticalPoints (Vector 7) P.function,
        0 < P.function p → P.function p < P.function q →
          nativeMorseIndex (Vector 7) P.function p ≤ nativeMorseIndex (Vector 7) P.function q) ∧
      ∀ Q : S.ExcellentMorsePresentation,
        (criticalPoints (Vector 7) P.function).ncard ≤
          (criticalPoints (Vector 7) Q.function).ncard := by
  classical
  let C : ℕ → Prop := fun n => ∃ P : S.ExcellentMorsePresentation,
    (criticalPoints (Vector 7) P.function).ncard = n
  obtain ⟨P₀⟩ := S.nonempty_excellentMorsePresentation
  have hex : ∃ n, C n := ⟨(criticalPoints (Vector 7) P₀.function).ncard, P₀, rfl⟩
  obtain ⟨P, hcard⟩ := Nat.find_spec hex
  obtain ⟨Q, hcrit, _, _, horder, _⟩ := P.exists_positive_index_ordered
  refine ⟨Q, horder, ?_⟩
  intro R
  rw [hcrit, hcard]
  exact Nat.find_min' hex ⟨R, rfl⟩

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
