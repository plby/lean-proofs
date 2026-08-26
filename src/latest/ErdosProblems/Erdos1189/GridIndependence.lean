/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Independence of box events supported on disjoint coordinate sets.
Informal source: the dependency argument in BBMST Lemma 3.5.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.Grid
import ErdosProblems.Erdos1189.ProductIndependence
import Mathlib.Data.Fintype.Pi

namespace Erdos1189.Grid

open Finset

variable {ι α : Type*} {q : ι → ℕ}

def DependsOn (S : Finset (Point q)) (I : Finset ι) : Prop :=
  ∀ u v : Point q, (∀ i ∈ I, u i = v i) → (u ∈ S ↔ v ∈ S)

lemma DependsOn.mono {S : Finset (Point q)} {I J : Finset ι}
    (h : DependsOn S I) (hIJ : I ⊆ J) : DependsOn S J :=
  fun u v huv => h u v (fun i hi => huv i (hIJ hi))

variable [Fintype ι] [DecidableEq ι]

lemma DependsOn.card_independent {S T : Finset (Point q)} {I J : Finset ι}
    (hS : DependsOn S I) (hT : DependsOn T J) (hIJ : Disjoint I J) :
    (S ∩ T).card * Fintype.card (Point q) = S.card * T.card := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ I) (fun i => Fin (q i))
  apply equiv_event_card_independent e S T
  · intro u v huv
    apply hS u v
    intro i hi
    exact congrFun huv ⟨i, hi⟩
  · intro u v huv
    apply hT u v
    intro j hj
    have hjI : j ∉ I := fun hjI => disjoint_left.mp hIJ hjI hj
    exact congrFun huv ⟨j, hjI⟩

noncomputable def boxEvent (H : Box q) : Finset (Point q) := by
  classical
  exact univ.filter (Contains H)

lemma mem_boxEvent {H : Box q} {u : Point q} : u ∈ boxEvent H ↔ Contains H u := by
  classical
  simp [boxEvent]

lemma boxEvent_depends (H : Box q) : DependsOn (boxEvent H) (fixed H) := by
  intro u v huv
  rw [mem_boxEvent, mem_boxEvent]
  constructor
  · intro hu i w hiw
    exact (huv i (mem_fixed.mpr ⟨w, hiw⟩)).symm.trans (hu i w hiw)
  · intro hv i w hiw
    exact (huv i (mem_fixed.mpr ⟨w, hiw⟩)).trans (hv i w hiw)

lemma avoidingBoxes_depends (H : α → Box q) (A : Finset α) :
    DependsOn (avoidingEvents (fun a => boxEvent (H a)) A) (familyFixed H A) := by
  intro u v huv
  rw [mem_avoidingEvents, mem_avoidingEvents]
  have hiff : ∀ a ∈ A, u ∈ boxEvent (H a) ↔ v ∈ boxEvent (H a) := by
    intro a ha
    apply boxEvent_depends (H a) u v
    intro i hi
    exact huv i (mem_familyFixed.mpr ⟨a, ha, hi⟩)
  constructor
  · intro hu a ha hv
    exact hu a ha ((hiff a ha).mpr hv)
  · intro hv a ha hu
    exact hv a ha ((hiff a ha).mp hu)

end Erdos1189.Grid
