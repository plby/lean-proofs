import ErdosProblems.Erdos556.DenseCore
import ErdosProblems.Erdos556.IsoDeletion

/-!
# Surviving vertices of an induced core

This identifies deletion inside a finite induced core with one induced
subgraph in the original vertex type, preserving all graph properties by
an explicit isomorphism.
-/

namespace Erdos556

open SimpleGraph Finset

def induceSetCongr {V : Type*} (G : SimpleGraph V) (S T : Set V) (h : S = T) :
    G.induce S ≃g G.induce T := by
  subst T
  exact SimpleGraph.Iso.refl

def survivingCore {V : Type*} [DecidableEq V] (S : Finset V) (T : Finset S) : Finset V :=
  Tᶜ.map (Function.Embedding.subtype (fun v => v ∈ S))

theorem survivingCore_subset {V : Type*} [DecidableEq V] (S : Finset V) (T : Finset S) :
    survivingCore S T ⊆ S := by
  intro x hx
  obtain ⟨y, _, hyx⟩ := mem_map.mp hx
  exact hyx ▸ y.property

theorem card_survivingCore {V : Type*} [DecidableEq V] (S : Finset V) (T : Finset S) :
    (survivingCore S T).card = S.card - T.card := by
  simp only [survivingCore, card_map, card_compl, Fintype.card_coe]

noncomputable def induceSurvivingCoreIso {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (T : Finset S) :
    (G.induce (S : Set V)).induce (T : Set S)ᶜ ≃g
      G.induce (survivingCore S T : Set V) :=
  (induceSetCongr (G.induce (S : Set V)) (T : Set S)ᶜ
    (↑(Tᶜ : Finset S) : Set S) (Finset.coe_compl T).symm).trans
      (induceFinsetMapIso G S Tᶜ)

#print axioms induceSurvivingCoreIso

end Erdos556
