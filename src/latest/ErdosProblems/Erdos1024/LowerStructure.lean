/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1024.LowerMatching

/-!
# Local structure of a linear triangle-free triple system

This is the deterministic part of the Kostochka--Mubayi--Verstraëte
argument.  After conditioning outside the closed neighborhood of a vertex,
the remaining admissible neighbors form an independent set and the edges
through the vertex form a matching.
-/

namespace Erdos1024
namespace Lower

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev System (V : Type*) := Finset (Finset V)

def ThreeUniform (H : System V) : Prop :=
  ∀ e ∈ H, e.card = 3

def Linear (H : System V) : Prop :=
  ∀ ⦃e⦄, e ∈ H → ∀ ⦃f⦄, f ∈ H → e ≠ f → (e ∩ f).card ≤ 1

def Independent (H : System V) (I : Finset V) : Prop :=
  ∀ ⦃e⦄, e ∈ H → ¬ e ⊆ I

instance independentDecidable (H : System V) (I : Finset V) :
    Decidable (Independent H I) := by
  unfold Independent
  infer_instance

/-- A loose triangle: the three pairwise intersections are singletons, but
there is no common vertex. -/
def HasLooseTriangle (H : System V) : Prop :=
  ∃ e ∈ H, ∃ f ∈ H, ∃ g ∈ H,
    e ≠ f ∧ e ≠ g ∧ f ≠ g ∧
    (e ∩ f).card = 1 ∧ (e ∩ g).card = 1 ∧
    (f ∩ g).card = 1 ∧ (e ∩ f ∩ g).card = 0

def TriangleFree (H : System V) : Prop :=
  ¬ HasLooseTriangle H

def neighborhood (H : System V) (v : V) : Finset V :=
  Finset.univ.filter fun u ↦
    u ≠ v ∧ ∃ e ∈ H, v ∈ e ∧ u ∈ e

@[simp] lemma mem_neighborhood {H : System V} {v u : V} :
    u ∈ neighborhood H v ↔ u ≠ v ∧ ∃ e ∈ H, v ∈ e ∧ u ∈ e := by
  simp [neighborhood]

@[simp] lemma not_mem_neighborhood_self (H : System V) (v : V) :
    v ∉ neighborhood H v := by simp

def closedNeighborhood (H : System V) (v : V) : Finset V :=
  insert v (neighborhood H v)

def outsidePart (H : System V) (v : V) (I : Finset V) : Finset V :=
  I \ closedNeighborhood H v

/-- Neighbors which may individually be adjoined to the conditioned
outside part. -/
def available (H : System V) (v : V) (R : Finset V) : Finset V :=
  (neighborhood H v).filter fun u ↦ Independent H (insert u R)

@[simp] lemma mem_available {H : System V} {v u : V} {R : Finset V} :
    u ∈ available H v R ↔
      u ∈ neighborhood H v ∧ Independent H (insert u R) := by
  simp [available]

/-- The two-vertex remainders of edges through `v` whose remainder lies in
`J`. -/
def linkPairs (H : System V) (v : V) (J : Finset V) :
    Finset (Finset V) :=
  (H.filter fun e ↦ v ∈ e ∧ e.erase v ⊆ J).image fun e ↦ e.erase v

lemma mem_linkPairs {H : System V} {v : V} {J a : Finset V} :
    a ∈ linkPairs H v J ↔
      ∃ e ∈ H, v ∈ e ∧ e.erase v ⊆ J ∧ e.erase v = a := by
  classical
  simp [linkPairs, and_assoc]

lemma linkPairs_subset {H : System V} {v : V} {J : Finset V}
    {a : Finset V} (ha : a ∈ linkPairs H v J) : a ⊆ J := by
  obtain ⟨e, -, -, heJ, rfl⟩ := mem_linkPairs.mp ha
  exact heJ

lemma linkPairs_card_two {H : System V} (h3 : ThreeUniform H)
    {v : V} {J : Finset V} {a : Finset V} (ha : a ∈ linkPairs H v J) :
    a.card = 2 := by
  obtain ⟨e, heH, hve, -, rfl⟩ := mem_linkPairs.mp ha
  rw [Finset.card_erase_of_mem hve, h3 e heH]

lemma linkPairs_pairwiseDisjoint {H : System V} (hlin : Linear H)
    {v : V} {J : Finset V} :
    (linkPairs H v J : Set (Finset V)).PairwiseDisjoint id := by
  classical
  intro a ha b hb hab
  change Disjoint a b
  rw [Finset.disjoint_left]
  intro x hxa hxb
  obtain ⟨e, heH, hve, -, hea⟩ := mem_linkPairs.mp ha
  obtain ⟨f, hfH, hvf, -, hfb⟩ := mem_linkPairs.mp hb
  have hxe : x ∈ e := Finset.mem_of_mem_erase (hea ▸ hxa)
  have hxf : x ∈ f := Finset.mem_of_mem_erase (hfb ▸ hxb)
  have hxv : x ≠ v := (Finset.mem_erase.mp (hea ▸ hxa)).1
  have htwo : 2 ≤ (e ∩ f).card := by
    have hsub : ({v, x} : Finset V) ⊆ e ∩ f := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · simp [hve, hvf]
      · simp [hxe, hxf]
    have hc := Finset.card_le_card hsub
    simpa [hxv, Ne.symm hxv] using hc
  have hef : e = f := by
    by_contra hne
    exact (not_lt_of_ge htwo) (lt_of_le_of_lt (hlin heH hfH hne) (by omega))
  apply hab
  rw [← hea, ← hfb, hef]

lemma vertex_of_edge_neighborhood {H : System V} {v x : V} {e : Finset V}
    (heH : e ∈ H) (hve : v ∈ e) (hxe : x ∈ e) (hxv : x ≠ v) :
    x ∈ neighborhood H v := by
  exact mem_neighborhood.mpr ⟨hxv, e, heH, hve, hxe⟩

lemma vertex_not_mem_of_disjoint_closed {H : System V} {v : V} {R : Finset V}
    (hdisj : Disjoint R (closedNeighborhood H v)) : v ∉ R := by
  intro hvR
  exact Finset.disjoint_left.mp hdisj hvR (by simp [closedNeighborhood])

lemma available_ne_self {H : System V} {v u : V} {R : Finset V}
    (hu : u ∈ available H v R) : u ≠ v :=
  (mem_neighborhood.mp (mem_available.mp hu).1).1

/-- The admissible neighbor set after conditioning is independent.  This is
exactly where loose triangles have to be deleted. -/
theorem independent_union_available {H : System V}
    (hlin : Linear H) (htri : TriangleFree H)
    {v : V} {R : Finset V} (hR : Independent H R)
    (hdisj : Disjoint R (closedNeighborhood H v)) :
    Independent H (R ∪ available H v R) := by
  classical
  intro e heH heSub
  have hnotR : ¬ e ⊆ R := hR heH
  obtain ⟨u, hue, huR⟩ := Set.not_subset.mp hnotR
  have huJ : u ∈ available H v R := by
    have := heSub hue
    exact (Finset.mem_union.mp this).resolve_left huR
  have hIndu := (mem_available.mp huJ).2
  have hnotInsert : ¬ e ⊆ insert u R := hIndu heH
  obtain ⟨w, hwe, hwInsert⟩ := Set.not_subset.mp hnotInsert
  have hwR : w ∉ R := fun hw ↦ hwInsert (Finset.mem_insert_of_mem hw)
  have hwu : w ≠ u := fun h ↦ hwInsert (h ▸ Finset.mem_insert_self u R)
  have hwJ : w ∈ available H v R := by
    have := heSub hwe
    exact (Finset.mem_union.mp this).resolve_left hwR
  obtain ⟨-, eu, heuH, hveu, hueu⟩ := mem_neighborhood.mp (mem_available.mp huJ).1
  obtain ⟨-, ew, hewH, hvew, hwew⟩ := mem_neighborhood.mp (mem_available.mp hwJ).1
  have hvR : v ∉ R := vertex_not_mem_of_disjoint_closed hdisj
  have hvJ : v ∉ available H v R := by
    intro hv
    exact (available_ne_self hv) rfl
  have hve : v ∉ e := by
    intro hve'
    have := heSub hve'
    rcases Finset.mem_union.mp this with h | h
    · exact hvR h
    · exact hvJ h
  have he_ne_eu : e ≠ eu := fun h ↦ hve (h ▸ hveu)
  have he_ne_ew : e ≠ ew := fun h ↦ hve (h ▸ hvew)
  have heu_ne_ew : eu ≠ ew := by
    intro hEq
    have hsub : ({u, w} : Finset V) ⊆ e ∩ eu := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hue, hueu⟩
      · exact Finset.mem_inter.mpr ⟨hwe, hEq ▸ hwew⟩
    have hcard : 2 ≤ (e ∩ eu).card := by
      have := Finset.card_le_card hsub
      simpa [hwu.symm] using this
    exact (not_lt_of_ge hcard) (lt_of_le_of_lt
      (hlin heH heuH he_ne_eu) (by omega))
  have hef_card : (e ∩ eu).card = 1 := by
    apply Nat.le_antisymm (hlin heH heuH he_ne_eu)
    exact Finset.one_le_card.mpr ⟨u, Finset.mem_inter.mpr ⟨hue, hueu⟩⟩
  have heg_card : (e ∩ ew).card = 1 := by
    apply Nat.le_antisymm (hlin heH hewH he_ne_ew)
    exact Finset.one_le_card.mpr ⟨w, Finset.mem_inter.mpr ⟨hwe, hwew⟩⟩
  have hfg_card : (eu ∩ ew).card = 1 := by
    apply Nat.le_antisymm (hlin heuH hewH heu_ne_ew)
    exact Finset.one_le_card.mpr ⟨v, by simp [hveu, hvew]⟩
  have htriple : (e ∩ eu ∩ ew).card = 0 := by
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx_e : x ∈ e := (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1
    have hx_eu : x ∈ eu := (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).2
    have hx_ew : x ∈ ew := (Finset.mem_inter.mp hx).2
    have hx_inter : x ∈ eu ∩ ew := Finset.mem_inter.mpr ⟨hx_eu, hx_ew⟩
    have hv_inter : v ∈ eu ∩ ew := Finset.mem_inter.mpr ⟨hveu, hvew⟩
    have hxv : x = v := by
      exact (Finset.card_le_one.mp hfg_card.le) x hx_inter v hv_inter
    exact hve (hxv ▸ hx_e)
  apply htri
  exact ⟨e, heH, eu, heuH, ew, hewH, he_ne_eu, he_ne_ew,
    heu_ne_ew, hef_card, heg_card, hfg_card, htriple⟩

end Lower
end Erdos1024

#print axioms Erdos1024.Lower.independent_union_available
