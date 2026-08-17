/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1024.LocalLemma
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Prod

/-!
# Independence of finite coordinate cylinders

Events depending on disjoint coordinate sets are independent under the
uniform distribution on a finite function space.  The proof is an explicit
coordinate-mixing bijection, so no measure-theoretic product-space machinery
is needed.
-/

namespace Erdos1024
namespace Cylinder

open LocalLemma

variable {Coordinate Value ι : Type*}

/-- Use `left` on coordinates in `S` and `right` elsewhere. -/
def mix [DecidableEq Coordinate] (S : Finset Coordinate)
    (left right : Coordinate → Value) : Coordinate → Value :=
  fun c ↦ if c ∈ S then left c else right c

@[simp] lemma mix_apply_of_mem [DecidableEq Coordinate]
    {S : Finset Coordinate} {left right : Coordinate → Value}
    {c : Coordinate} (hc : c ∈ S) :
    mix S left right c = left c := by
  simp [mix, hc]

@[simp] lemma mix_apply_of_not_mem [DecidableEq Coordinate]
    {S : Finset Coordinate} {left right : Coordinate → Value}
    {c : Coordinate} (hc : c ∉ S) :
    mix S left right c = right c := by
  simp [mix, hc]

/-- Membership of `A` is determined by the coordinates in `S`. -/
def DependsOn [DecidableEq Coordinate] [DecidableEq (Coordinate → Value)]
    (A : Finset (Coordinate → Value)) (S : Finset Coordinate) : Prop :=
  ∀ f g, (∀ c ∈ S, f c = g c) → (f ∈ A ↔ g ∈ A)

section TwoEvents

variable [Fintype Coordinate] [DecidableEq Coordinate]
variable [Fintype Value] [Nonempty Value] [DecidableEq Value]

/-- The coordinate-mixing bijection underlying cylinder independence. -/
noncomputable def mixingEquiv
    (A B : Finset (Coordinate → Value)) (S T : Finset Coordinate)
    (hA : DependsOn A S) (hB : DependsOn B T) (hST : Disjoint S T) :
    ({f // f ∈ A ∩ B} × (Coordinate → Value)) ≃
      ({f // f ∈ A} × {f // f ∈ B}) where
  toFun z := by
    let omega : Coordinate → Value := z.1.1
    let eta : Coordinate → Value := z.2
    have homegaA : omega ∈ A := (Finset.mem_inter.mp z.1.2).1
    have homegaB : omega ∈ B := (Finset.mem_inter.mp z.1.2).2
    have ha : mix T eta omega ∈ A := by
      apply (hA omega (mix T eta omega) ?_).mp homegaA
      intro c hcS
      have hcT : c ∉ T := Finset.disjoint_left.mp hST hcS
      simp [mix, hcT]
    have hb : mix T omega eta ∈ B := by
      apply (hB omega (mix T omega eta) ?_).mp homegaB
      intro c hcT
      simp [mix, hcT]
    exact ⟨⟨mix T eta omega, ha⟩, ⟨mix T omega eta, hb⟩⟩
  invFun z := by
    let a : Coordinate → Value := z.1.1
    let b : Coordinate → Value := z.2.1
    have ha : a ∈ A := z.1.2
    have hb : b ∈ B := z.2.2
    have homegaA : mix T b a ∈ A := by
      apply (hA a (mix T b a) ?_).mp ha
      intro c hcS
      have hcT : c ∉ T := Finset.disjoint_left.mp hST hcS
      simp [mix, hcT]
    have homegaB : mix T b a ∈ B := by
      apply (hB b (mix T b a) ?_).mp hb
      intro c hcT
      simp [mix, hcT]
    exact ⟨⟨mix T b a, Finset.mem_inter.mpr ⟨homegaA, homegaB⟩⟩,
      mix T a b⟩
  left_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      funext c
      by_cases hc : c ∈ T <;> simp [mix, hc]
    · funext c
      by_cases hc : c ∈ T <;> simp [mix, hc]
  right_inv z := by
    apply Prod.ext <;> apply Subtype.ext <;> funext c <;>
      by_cases hc : c ∈ T <;> simp [mix, hc]

/-- Two events on a finite function space are independent when their
coordinate supports are disjoint. -/
theorem uniformProbability_inter_eq_mul
    (A B : Finset (Coordinate → Value)) (S T : Finset Coordinate)
    (hA : DependsOn A S) (hB : DependsOn B T) (hST : Disjoint S T) :
    uniformProbability (A ∩ B) = uniformProbability A * uniformProbability B := by
  have hcard := Fintype.card_congr (mixingEquiv A B S T hA hB hST)
  simp only [Fintype.card_prod, Fintype.card_coe] at hcard
  unfold uniformProbability
  have hne : (Fintype.card (Coordinate → Value) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos.ne' : Fintype.card (Coordinate → Value) ≠ 0)
  field_simp
  exact_mod_cast hcard

end TwoEvents

section CoordinateConstraints

variable [Fintype Coordinate] [DecidableEq Coordinate]
variable [Fintype Value] [Nonempty Value] [DecidableEq Value]

/-- Functions whose value at `c` lies in `R`. -/
def coordinateEvent (c : Coordinate) (R : Finset Value) :
    Finset (Coordinate → Value) :=
  Finset.univ.filter fun f ↦ f c ∈ R

/-- Functions whose values on every coordinate of `S` lie in `R`. -/
def constraintEvent (S : Finset Coordinate) (R : Finset Value) :
    Finset (Coordinate → Value) :=
  Finset.univ.filter fun f ↦ ∀ c ∈ S, f c ∈ R

lemma coordinateEvent_dependsOn (c : Coordinate) (R : Finset Value) :
    DependsOn (coordinateEvent c R) {c} := by
  intro f g hfg
  simp only [coordinateEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hfg c (Finset.mem_singleton_self c)]

lemma constraintEvent_dependsOn (S : Finset Coordinate) (R : Finset Value) :
    DependsOn (constraintEvent S R) S := by
  intro f g hfg
  simp only [constraintEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hf c hc
    rw [← hfg c hc]
    exact hf c hc
  · intro hg c hc
    rw [hfg c hc]
    exact hg c hc

/-- Splitting off coordinate `c` identifies the one-coordinate event with
an allowed value and an arbitrary assignment on all other coordinates. -/
noncomputable def coordinateEventEquiv (c : Coordinate) (R : Finset Value) :
    {f // f ∈ coordinateEvent c R} ≃
      ({v // v ∈ R} × ({d : Coordinate // d ≠ c} → Value)) where
  toFun f :=
    ⟨⟨f.1 c, (Finset.mem_filter.mp f.2).2⟩, fun d ↦ f.1 d⟩
  invFun z := by
    let f := (Equiv.funSplitAt c Value).symm (z.1.1, z.2)
    refine ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    change f c ∈ R
    simpa [f] using z.1.2
  left_inv f := by
    apply Subtype.ext
    exact (Equiv.funSplitAt c Value).left_inv f.1
  right_inv z := by
    have h := (Equiv.funSplitAt c Value).right_inv (z.1.1, z.2)
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst h
    · change ((Equiv.funSplitAt c Value)
          ((Equiv.funSplitAt c Value).symm (z.1.1, z.2))).2 = z.2
      exact congrArg Prod.snd h

/-- Exact probability of a one-coordinate constraint. -/
theorem uniformProbability_coordinateEvent (c : Coordinate) (R : Finset Value) :
    uniformProbability (coordinateEvent c R) =
      (R.card : ℝ) / Fintype.card Value := by
  let Rest := {d : Coordinate // d ≠ c} → Value
  have hevent := Fintype.card_congr (coordinateEventEquiv c R)
  have hall := Fintype.card_congr (Equiv.funSplitAt c Value)
  simp only [Fintype.card_prod, Fintype.card_coe] at hevent hall
  have hrest : 0 < Fintype.card Rest := Fintype.card_pos
  have hvalue : 0 < Fintype.card Value := Fintype.card_pos
  unfold uniformProbability
  rw [show ((coordinateEvent c R).card : ℝ) =
      (R.card : ℝ) * Fintype.card Rest by exact_mod_cast hevent]
  rw [show (Fintype.card (Coordinate → Value) : ℝ) =
      (Fintype.card Value : ℝ) * Fintype.card Rest by exact_mod_cast hall]
  field_simp

lemma constraintEvent_empty (R : Finset Value) :
    constraintEvent (∅ : Finset Coordinate) R = Finset.univ := by
  ext f
  simp [constraintEvent]

lemma constraintEvent_insert {c : Coordinate} {S : Finset Coordinate}
    (R : Finset Value) :
    constraintEvent (insert c S) R =
      coordinateEvent c R ∩ constraintEvent S R := by
  ext f
  simp [constraintEvent, coordinateEvent]

/-- Exact product probability for identical allowed-value constraints on a
finite coordinate set. -/
theorem uniformProbability_constraintEvent (S : Finset Coordinate)
    (R : Finset Value) :
    uniformProbability (constraintEvent S R) =
      ((R.card : ℝ) / Fintype.card Value) ^ S.card := by
  induction S using Finset.induction with
  | empty =>
      rw [constraintEvent_empty, uniformProbability_univ]
      simp
  | @insert c S hc ih =>
      rw [constraintEvent_insert]
      rw [uniformProbability_inter_eq_mul
        (coordinateEvent c R) (constraintEvent S R) {c} S
        (coordinateEvent_dependsOn c R) (constraintEvent_dependsOn S R)
        (Finset.disjoint_singleton_left.mpr hc)]
      rw [uniformProbability_coordinateEvent, ih, Finset.card_insert_of_notMem hc]
      rw [pow_succ]
      exact mul_comm _ _

end CoordinateConstraints

section EventFamily

variable [Fintype Coordinate] [DecidableEq Coordinate]
variable [Fintype Value] [Nonempty Value] [DecidableEq Value]
variable [Fintype ι] [DecidableEq ι]

lemma avoiding_dependsOn_biUnion
    (event : ι → Finset (Coordinate → Value))
    (support : ι → Finset Coordinate)
    (hdepends : ∀ i, DependsOn (event i) (support i))
    (J : Finset ι) :
    DependsOn (avoiding event J) (J.biUnion support) := by
  intro f g hfg
  simp only [avoiding, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hf j hj hgj
    apply hf j hj
    apply (hdepends j f g ?_).mpr hgj
    intro c hc
    exact hfg c (Finset.mem_biUnion.mpr ⟨j, hj, hc⟩)
  · intro hg j hj hfj
    apply hg j hj
    apply (hdepends j f g ?_).mp hfj
    intro c hc
    exact hfg c (Finset.mem_biUnion.mpr ⟨j, hj, hc⟩)

lemma disjoint_biUnion_of_pairwise_disjoint
    (support : ι → Finset Coordinate) {i : ι} {J : Finset ι}
    (h : ∀ j ∈ J, Disjoint (support i) (support j)) :
    Disjoint (support i) (J.biUnion support) := by
  rw [Finset.disjoint_left]
  intro c hci hcJ
  obtain ⟨j, hj, hcj⟩ := Finset.mem_biUnion.mp hcJ
  exact Finset.disjoint_left.mp (h j hj) hci hcj

/-- An event is independent of simultaneous avoidance of a family of events
whose supports are all disjoint from its support. -/
theorem uniformProbability_event_inter_avoiding
    (event : ι → Finset (Coordinate → Value))
    (support : ι → Finset Coordinate)
    (hdepends : ∀ i, DependsOn (event i) (support i))
    (i : ι) (J : Finset ι)
    (hdisjoint : ∀ j ∈ J, Disjoint (support i) (support j)) :
    uniformProbability (event i ∩ avoiding event J) =
      uniformProbability (event i) * uniformProbability (avoiding event J) := by
  exact uniformProbability_inter_eq_mul
    (event i) (avoiding event J) (support i) (J.biUnion support)
    (hdepends i) (avoiding_dependsOn_biUnion event support hdepends J)
    (disjoint_biUnion_of_pairwise_disjoint support hdisjoint)

end EventFamily

end Cylinder
end Erdos1024

#print axioms Erdos1024.Cylinder.uniformProbability_event_inter_avoiding
