import Mathlib
import ErdosProblems.Erdos550.DeferredSeedAttachments
import ErdosProblems.Erdos550.TauFineComponentIndexing

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Component demand at the two head colours

After parity refinement, a component is routed according to the colour of its
upper seed.  These definitions record the two total demands and their exact
sum.
-/

open Finset

namespace Erdos550

open Classical

variable {A : Type} [Fintype A] [DecidableEq A]

noncomputable def componentHeadColour
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (col : A → Bool)
    (c : NonseedComponent T S) : Bool :=
  col (componentUpperSeed T S D c)

noncomputable def componentHeadDemand
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (col : A → Bool) (head : Bool) : ℝ :=
  ∑ c ∈ Finset.univ.filter
      (fun c : NonseedComponent T S =>
        componentHeadColour T S D col c = head),
    ((componentNonseedVertices T S c.1).card : ℝ)

/-- Route colour of a source vertex.  Seeds use their own head colour; every
nonseed uses the colour assigned to its entire deleted component. -/
noncomputable def parityRouteColour
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (col : A → Bool) (x : A) : Bool :=
  if hx : x ∈ S then col x
  else componentHeadColour T S D col
    (nonseedComponentOf T S x hx)

lemma parityRouteColour_component
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (col : A → Bool)
    (c : NonseedComponent T S)
    {x : A} (hx : x ∈ componentNonseedVertices T S c.1) :
    parityRouteColour T S D col x =
      componentHeadColour T S D col c := by
  have hxNot : x ∉ S :=
    (mem_componentNonseedVertices_iff T S c.1 x).mp hx |>.1
  rw [parityRouteColour, dif_neg hxNot]
  have hc :
      nonseedComponentOf T S x hxNot = c :=
    by
      obtain ⟨hx', hc'⟩ :=
        (mem_indexed_component_iff T S c x).mp hx
      simpa using! hc'
  rw [hc]

/-- Equivalent vertex-level demand, convenient for state/load accounting. -/
noncomputable def parityRouteDemand
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (col : A → Bool) (head : Bool) : ℝ :=
  ((Finset.univ.filter fun x =>
    x ∉ S ∧ parityRouteColour T S D col x = head).card : ℝ)

lemma parityRouteDemand_nonneg
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (col : A → Bool) (head : Bool) :
    0 ≤ parityRouteDemand T S D col head := by
  exact Nat.cast_nonneg _

lemma parityRouteDemand_pos_of_component
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (col : A → Bool)
    (c : NonseedComponent T S) :
    0 < parityRouteDemand T S D col
      (componentHeadColour T S D col c) := by
  let x := D.root c
  have hxNonseed : x ∉ S := by
    exact (mem_componentNonseedVertices_iff T S c.1 x).mp
      (D.root_mem c) |>.1
  have hxRoute :
      parityRouteColour T S D col x =
        componentHeadColour T S D col c :=
    parityRouteColour_component T S D col c (D.root_mem c)
  rw [parityRouteDemand]
  exact_mod_cast Finset.card_pos.mpr
    (show (Finset.univ.filter (fun y =>
      y ∉ S ∧ parityRouteColour T S D col y =
        componentHeadColour T S D col c)).Nonempty by
      exact ⟨x, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hxNonseed, hxRoute⟩⟩)

lemma route_filter_card_eq_parityRouteDemand
    (T : SimpleGraph A) (S P : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (col : A → Bool) (head : Bool) :
    ((P.filter fun x =>
      x ∉ S ∧ parityRouteColour T S D col x = head).card : ℝ) ≤
        parityRouteDemand T S D col head := by
  rw [parityRouteDemand]
  exact_mod_cast Finset.card_le_card
    (show
      P.filter (fun x =>
        x ∉ S ∧ parityRouteColour T S D col x = head) ⊆
      Finset.univ.filter (fun x =>
        x ∉ S ∧ parityRouteColour T S D col x = head) by
      intro x hx
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩)

lemma parityRouteDemand_false_add_true
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (col : A → Bool) :
    parityRouteDemand T S D col false +
        parityRouteDemand T S D col true =
      (Fintype.card A - S.card : ℕ) := by
  let F := Finset.univ.filter fun x =>
    x ∉ S ∧ parityRouteColour T S D col x = false
  let R := Finset.univ.filter fun x =>
    x ∉ S ∧ parityRouteColour T S D col x = true
  have hdisj : Disjoint F R := by
    rw [Finset.disjoint_left]
    intro x hxF hxR
    have hf := (Finset.mem_filter.mp hxF).2.2
    have hr := (Finset.mem_filter.mp hxR).2.2
    simp_all
  have hunion : F ∪ R = Finset.univ \ S := by
    ext x
    cases h : parityRouteColour T S D col x <;>
      simp [F, R, h]
  have hcard : F.card + R.card = Fintype.card A - S.card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion,
      Finset.card_sdiff_of_subset (Finset.subset_univ S),
      Finset.card_univ]
  have hcast := congrArg (fun n : ℕ => (n : ℝ)) hcard
  simpa only [parityRouteDemand, F, R, Nat.cast_add,
    Nat.cast_sub (Finset.card_le_univ S)] using! hcast

lemma componentHeadDemand_nonneg
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (col : A → Bool) (head : Bool) :
    0 ≤ componentHeadDemand T S D col head := by
  exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

lemma componentHeadDemand_false_add_true
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (col : A → Bool) :
    componentHeadDemand T S D col false +
        componentHeadDemand T S D col true =
      (Fintype.card A - S.card : ℕ) := by
  let F := Finset.univ.filter
    (fun c : NonseedComponent T S =>
      componentHeadColour T S D col c = false)
  let R := Finset.univ.filter
    (fun c : NonseedComponent T S =>
      componentHeadColour T S D col c = true)
  have hdisj : Disjoint F R := by
    rw [Finset.disjoint_left]
    intro c hcF hcR
    have hf := (Finset.mem_filter.mp hcF).2
    have hr := (Finset.mem_filter.mp hcR).2
    simp_all
  have hunion :
      F ∪ R =
        (Finset.univ : Finset (NonseedComponent T S)) := by
    ext c
    cases h : componentHeadColour T S D col c <;>
      simp [F, R, h]
  calc
    componentHeadDemand T S D col false +
        componentHeadDemand T S D col true =
      (∑ c ∈ F, ((componentNonseedVertices T S c.1).card : ℝ)) +
        ∑ c ∈ R, ((componentNonseedVertices T S c.1).card : ℝ) := by
          rfl
    _ = ∑ c ∈ F ∪ R,
        ((componentNonseedVertices T S c.1).card : ℝ) := by
          rw [Finset.sum_union hdisj]
    _ = ∑ c : NonseedComponent T S,
        ((componentNonseedVertices T S c.1).card : ℝ) := by
          rw [hunion]
    _ = (Fintype.card A - S.card : ℕ) := by
          have hnat := sum_componentNonseedVertices_card T S
          have hcast := congrArg (fun n : ℕ => (n : ℝ)) hnat
          simpa only [Nat.cast_sum,
            Nat.cast_sub (Finset.card_le_univ S)] using! hcast

end Erdos550
