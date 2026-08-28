import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenState

/-!
# Actual one- or two-step descent in finite positive-half third homology

Every recorded strict or primitive surgery is an actual state step.
The general exceptional trichotomy therefore gives a finite path with
strictly smaller positive-half H3 cardinality and finite closed H3 at
its endpoint. Its intermediate free state is not required to be finite.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere GLOrthonormalization SevenSurgery
open SingularMayerVietoris FramedAttachingProduct UnitSurgery

variable {B : Type} [TopologicalSpace B] (S : CollaredSevenState B)

theorem successor_of_primitive (N : ℕ)
    (h : TimeCollar.HasPrimitiveReduction S.embedding S.normalFrame S.time N) :
    ∃ U : CollaredSevenState B, S.Step U ∧ Finite (SingularHomology U.Space 3) ∧
      U.thirdCard = N := by
  obtain ⟨f, A, hA, T, hT, _, hcard, _, _, _, _, hfinite⟩ := h
  exact ⟨S.perform A hA T hT, S.step_perform A hA T hT, hfinite, hcard⟩

variable [Finite (SingularHomology S.Space 3)]

theorem successor_of_strict (v : Sphere 3)
    (h : TimeCollar.HasStrictReduction S.embedding S.normalFrame S.time v) :
    ∃ U : CollaredSevenState B, S.Step U ∧ Finite (SingularHomology U.Space 3) ∧
      U.thirdCard < S.thirdCard := by
  obtain ⟨f, A, hA, T, hT, j, Q, hfinite, hlt, _, _, _⟩ := h
  let : Finite (SingularHomology
      (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3) := hfinite
  exact ⟨S.perform Q.twisted Q.twisted_radius (Q.twistedTimeData hA T) hT,
    S.step_perform Q.twisted Q.twisted_radius (Q.twistedTimeData hA T) hT,
    S.perform_finite_third Q.twisted Q.twisted_radius (Q.twistedTimeData hA T) hT, hlt⟩

theorem successors_of_exceptional (v : Sphere 3)
    (h : TimeCollar.HasExceptionalSurgery S.embedding S.normalFrame S.time v) :
    ∃ U V : CollaredSevenState B, S.Step U ∧ U.Step V ∧
      Finite (SingularHomology V.Space 3) ∧ V.thirdCard < S.thirdCard := by
  obtain ⟨f, A, hA, T, hT, j, Q, _, _, hout⟩ := h
  let U := S.perform Q.twisted Q.twisted_radius (Q.twistedTimeData hA T) hT
  have hSU : S.Step U := S.step_perform Q.twisted Q.twisted_radius (Q.twistedTimeData hA T) hT
  rcases hout with ⟨x, σ, _, hfinite, _, hcard, hnext⟩ |
      ⟨hfinite, _, hcard, _, hnext⟩
  · have hn : TimeCollar.HasPrimitiveReduction U.embedding U.normalFrame U.time
        (Nat.card σ.ker) := hnext
    obtain ⟨V, hUV, hFV, hV⟩ := U.successor_of_primitive (Nat.card σ.ker) hn
    refine ⟨U, V, hSU, hUV, hFV, ?_⟩
    let : Finite σ.ker := hfinite
    have hp : 0 < Nat.card σ.ker := Nat.card_pos
    change V.thirdCard < Nat.card (SingularHomology (TimeCollar.NonnegativeHalf S.time) 3)
    rw [hV]
    omega
  · let : Finite (SingularHomology
        (PositiveHalf Q.twisted Q.twisted_radius (Q.twistedTimeData hA T)) 3) := hfinite
    let : Finite (SingularHomology U.Space 3) :=
      S.perform_finite_third Q.twisted Q.twisted_radius (Q.twistedTimeData hA T) hT
    have hn : TimeCollar.HasStrictReduction U.embedding U.normalFrame U.time (spherePole 3) :=
      hnext (spherePole 3)
    obtain ⟨V, hUV, hFV, hV⟩ := U.successor_of_strict (spherePole 3) hn
    exact ⟨U, V, hSU, hUV, hFV, hV.trans_eq hcard⟩

variable [Subsingleton (SingularHomology B 2)] [Subsingleton (SingularHomology B 3)]
  [Subsingleton (SingularHomology B 4)]

theorem reducing_path_or_zero :
    (∃ U : CollaredSevenState B, S.Reachable U ∧ Finite (SingularHomology U.Space 3) ∧
      U.thirdCard < S.thirdCard) ∨
      Subsingleton (SingularHomology (TimeCollar.NonnegativeHalf S.time) 3) := by
  rcases S.collar.torsion_surgery_or_zero S.embedding S.normalFrame
      S.time_smooth S.time_regular (spherePole 3) with h | h | h
  · obtain ⟨U, hSU, hfinite, hlt⟩ := S.successor_of_strict (spherePole 3) h
    exact Or.inl ⟨U, Relation.ReflTransGen.single hSU, hfinite, hlt⟩
  · obtain ⟨U, V, hSU, hUV, hfinite, hlt⟩ := S.successors_of_exceptional (spherePole 3) h
    exact Or.inl ⟨V, (Relation.ReflTransGen.single hSU).trans
      (Relation.ReflTransGen.single hUV), hfinite, hlt⟩
  · exact Or.inr h

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
