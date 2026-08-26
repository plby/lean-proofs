import ErdosProblems.Erdos73.ParityPaths
import ErdosProblems.Erdos73.DegreeTwoPaths
import ErdosProblems.Erdos73.PackingCopy

/-! Pendant terminals change ordinary path parity by a prescribed Boolean potential. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [DecidableEq V]

def parityPendantGraph (G : SimpleGraph V) (T : Finset V) (c : V → Bool) :
    SimpleGraph (V ⊕ V) where
  Adj x y := match x, y with
    | .inl a, .inl b => G.Adj a b
    | .inl a, .inr b => a = b ∧ b ∈ T ∧ c b = true
    | .inr a, .inl b => b = a ∧ a ∈ T ∧ c a = true
    | .inr _, .inr _ => False
  symm := ⟨by
    intro x y h
    cases x <;> cases y
    · exact h.symm
    · exact h
    · exact h
    · exact h⟩
  loopless := ⟨by
    intro x h
    cases x
    · exact G.irrefl h
    · exact h⟩

def pendantProjection : V ⊕ V → V := Sum.elim id id

def pendantTerminal (c : V → Bool) (v : V) : V ⊕ V :=
  if c v then Sum.inr v else Sum.inl v

theorem pendantProjection_terminal (c : V → Bool) (v : V) :
    pendantProjection (pendantTerminal c v) = v := by
  simp only [pendantTerminal]
  split <;> rfl

theorem pendantTerminal_injective (c : V → Bool) : Function.Injective (pendantTerminal c) := by
  intro x y h
  simpa only [pendantProjection_terminal] using congrArg pendantProjection h

def parityPendantTerminals (T : Finset V) (c : V → Bool) : Finset (V ⊕ V) :=
  T.image (pendantTerminal c)

theorem mem_parityPendantTerminals (T : Finset V) (c : V → Bool) (x : V ⊕ V) :
    x ∈ parityPendantTerminals T c ↔
      pendantProjection x ∈ T ∧ x = pendantTerminal c (pendantProjection x) := by
  constructor
  · intro hx
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
    rw [pendantProjection_terminal]
    exact ⟨hv, rfl⟩
  · rintro ⟨hx, he⟩
    exact mem_image.mpr ⟨pendantProjection x, hx, he.symm⟩

@[simp] theorem inl_mem_parityPendantTerminals (T : Finset V) (c : V → Bool) (v : V) :
    Sum.inl v ∈ parityPendantTerminals T c ↔ v ∈ T ∧ c v = false := by
  rw [mem_parityPendantTerminals]
  change (v ∈ T ∧ Sum.inl v = pendantTerminal c v) ↔ _
  cases hc : c v <;> simp [pendantTerminal, hc]

@[simp] theorem inr_mem_parityPendantTerminals (T : Finset V) (c : V → Bool) (v : V) :
    Sum.inr v ∈ parityPendantTerminals T c ↔ v ∈ T ∧ c v = true := by
  rw [mem_parityPendantTerminals]
  change (v ∈ T ∧ Sum.inr v = pendantTerminal c v) ↔ _
  cases hc : c v <;> simp [pendantTerminal, hc]

def parityPendantCopy (G : SimpleGraph V) (T : Finset V) (c : V → Bool) :
    G.Copy (parityPendantGraph G T c) where
  toHom := ⟨Sum.inl, fun h => h⟩
  injective' := Sum.inl_injective

theorem parityPendant_leaf_adj {G : SimpleGraph V} {T : Finset V} {c : V → Bool}
    (v : V) (x : V ⊕ V) :
    (parityPendantGraph G T c).Adj (Sum.inr v) x ↔
      x = Sum.inl v ∧ v ∈ T ∧ c v = true := by
  cases x <;> simp [parityPendantGraph]

theorem parityPendant_leaf_endpoint {G : SimpleGraph V} {T : Finset V} {c : V → Bool}
    (P : GraphPath (parityPendantGraph G T c)) {v : V} (hv : Sum.inr v ∈ P.vertexSet) :
    Sum.inr v = P.source ∨ Sum.inr v = P.target := by
  by_contra hn
  push Not at hn
  obtain ⟨a, b, hab, ha, hb⟩ := P.internal_neighbors hv hn.1 hn.2
  have hea := (parityPendant_leaf_adj v a).mp (P.edgeSet_subset_edgeSet ha)
  have heb := (parityPendant_leaf_adj v b).mp (P.edgeSet_subset_edgeSet hb)
  exact hab (hea.1.trans heb.1.symm)

theorem parityPendant_projection_closed {G : SimpleGraph V} {T : Finset V} {c : V → Bool}
    (P : GraphPath (parityPendantGraph G T c)) (hne : P.source ≠ P.target)
    {x : V ⊕ V} (hx : x ∈ P.vertexSet) :
    Sum.inl (pendantProjection x) ∈ P.vertexSet := by
  cases x with
  | inl v => exact hx
  | inr v =>
    have hnil := P.walk_not_nil_of_source_ne_target hne
    rcases parityPendant_leaf_endpoint P hx with hs | ht
    · have hadj : (parityPendantGraph G T c).Adj (Sum.inr v) P.walk.snd := by
        simpa only [← hs] using P.walk.adj_snd hnil
      have he := ((parityPendant_leaf_adj v _).mp hadj).1
      exact he ▸ List.mem_toFinset.mpr (List.mem_of_mem_tail (P.walk.snd_mem_tail_support hnil))
    · have hadj : (parityPendantGraph G T c).Adj (Sum.inr v) P.walk.penultimate := by
        simpa only [← ht] using (P.walk.adj_penultimate hnil).symm
      have he := ((parityPendant_leaf_adj v _).mp hadj).1
      exact he ▸ P.penultimate_mem_vertexSet hne

end
end Erdos73
