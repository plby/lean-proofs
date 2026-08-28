import Wikipedia.NoExoticSixSphere.JamesPairWords
import Wikipedia.NoExoticSixSphere.JamesWordTopology
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Continuity of the actual second James--Hopf map

On each finite power of the source the formula is an explicitly ordered
finite word of paired coordinates. The final topology therefore supplies
joint continuity without assuming that multiplication on an arbitrary
James space is continuous.

The right-lexicographic convention agrees with the second James--Hopf
formula in Grbić and Wu, *Applications of combinatorial groups to Hopf
invariant and the exponent problem*, Algebraic & Geometric Topology 6
(2006), Section 3: https://www.personal.soton.ac.uk/jg1u11/Papers/Applications.pdf
-/

noncomputable section

namespace NoExoticSixSphere.James

variable {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
  (x₀ : X) (z₀ : Z) (b : X → X → Z)
  (hleft : ∀ x, b x₀ x = z₀) (hright : ∀ x, b x x₀ = z₀)
  (hc : Continuous (fun p : X × X ↦ b p.1 p.2))

omit [TopologicalSpace X] [TopologicalSpace Z] in
include hleft hright in
theorem secondHopf_array (n : ℕ) (v : Fin n → X) :
    secondHopf x₀ z₀ b (word x₀ (List.ofFn v)) =
      word z₀ ((pairs (List.ofFn (fun i : Fin n ↦ i))).map (fun p ↦ b (v p.1) (v p.2))) := by
  rw [secondHopf_word x₀ z₀ b hleft hright]
  have hv : List.ofFn v = (List.ofFn (fun i : Fin n ↦ i)).map v := List.ofFn_comp' _ _
  rw [hv, pairs_map, List.map_map]
  rfl

include hleft hright hc in
theorem continuous_secondHopf : Continuous (secondHopf x₀ z₀ b) := by
  apply (continuous_iff_on_words x₀ _).mpr
  intro n
  have hpair (p : Fin n × Fin n) :
      Continuous (fun v : Fin n → X ↦ b (v p.1) (v p.2)) := by
    have he : Continuous (fun v : Fin n → X ↦ (v p.1, v p.2)) :=
      (continuous_apply p.1).prodMk (continuous_apply p.2)
    exact hc.comp he
  have h := continuous_word_map z₀ (pairs (List.ofFn (fun i : Fin n ↦ i)))
    (fun (v : Fin n → X) p ↦ b (v p.1) (v p.2)) hpair
  have he : (fun v : Fin n → X ↦ secondHopf x₀ z₀ b (word x₀ (List.ofFn v))) =
      (fun v ↦ word z₀ ((pairs (List.ofFn (fun i : Fin n ↦ i))).map
        (fun p ↦ b (v p.1) (v p.2)))) :=
    funext (secondHopf_array x₀ z₀ b hleft hright n)
  exact he.symm ▸ h

def secondHopfMap : C(Space X x₀, Space Z z₀) :=
  ⟨secondHopf x₀ z₀ b, continuous_secondHopf x₀ z₀ b hleft hright hc⟩

theorem secondHopfMap_one : secondHopfMap x₀ z₀ b hleft hright hc 1 = 1 := rfl

theorem secondHopfMap_letter (x : X) :
    secondHopfMap x₀ z₀ b hleft hright hc (letter x₀ x) = 1 :=
  secondHopf_letter x₀ z₀ b hleft hright x

theorem secondHopfMap_two_letters (x y : X) :
    secondHopfMap x₀ z₀ b hleft hright hc (letter x₀ x * letter x₀ y) =
      letter z₀ (b x y) := secondHopf_two_letters x₀ z₀ b hleft hright x y

end NoExoticSixSphere.James
