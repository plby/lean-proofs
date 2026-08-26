import ErdosProblems.Erdos19.GraphMatching

/-! # The involution that swaps partners in a matching -/

namespace Erdos19

open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V : Type*} {G : _root_.SimpleGraph V}

noncomputable def matchingPartnerFun (M : G.Subgraph) (hM : M.IsMatching) (x : V) : V :=
  if hx : x ∈ M.verts then Classical.choose (hM hx) else x

theorem matchingPartnerFun_adj (M : G.Subgraph) (hM : M.IsMatching)
    {x : V} (hx : x ∈ M.verts) : M.Adj x (matchingPartnerFun M hM x) := by
  rw [matchingPartnerFun, dif_pos hx]
  exact (Classical.choose_spec (hM hx)).1

theorem matchingPartnerFun_of_not_mem (M : G.Subgraph) (hM : M.IsMatching)
    {x : V} (hx : x ∉ M.verts) : matchingPartnerFun M hM x = x := by
  rw [matchingPartnerFun, dif_neg hx]

theorem matchingPartnerFun_involutive (M : G.Subgraph) (hM : M.IsMatching) :
    Function.Involutive (matchingPartnerFun M hM) := by
  intro x
  by_cases hx : x ∈ M.verts
  · have hxy := matchingPartnerFun_adj M hM hx
    have hyz := matchingPartnerFun_adj M hM hxy.snd_mem
    exact hM.eq_of_adj_right hyz.symm hxy
  · rw [matchingPartnerFun_of_not_mem M hM hx, matchingPartnerFun_of_not_mem M hM hx]

noncomputable def matchingPartner (M : G.Subgraph) (hM : M.IsMatching) : V ≃ V :=
  { toFun := matchingPartnerFun M hM
    invFun := matchingPartnerFun M hM
    left_inv := matchingPartnerFun_involutive M hM
    right_inv := matchingPartnerFun_involutive M hM }

@[simp] theorem matchingPartner_apply_apply (M : G.Subgraph) (hM : M.IsMatching) (x : V) :
    matchingPartner M hM (matchingPartner M hM x) = x :=
  matchingPartnerFun_involutive M hM x

theorem matchingPartner_adj (M : G.Subgraph) (hM : M.IsMatching)
    {x : V} (hx : x ∈ M.verts) : M.Adj x (matchingPartner M hM x) :=
  matchingPartnerFun_adj M hM hx

@[simp] theorem matchingPartner_mem_iff (M : G.Subgraph) (hM : M.IsMatching) (x : V) :
    matchingPartner M hM x ∈ M.verts ↔ x ∈ M.verts := by
  constructor
  · intro hx
    have h := (matchingPartner_adj M hM hx).snd_mem
    simpa only [matchingPartner_apply_apply] using h
  · intro hx
    exact (matchingPartner_adj M hM hx).snd_mem

theorem matchingPartner_not_mem_of_not_mem_image (M : G.Subgraph) (hM : M.IsMatching)
    (Z : Set V) {x : V} (hx : x ∉ matchingPartner M hM '' Z) :
    matchingPartner M hM x ∉ Z := by
  intro h
  exact hx ⟨matchingPartner M hM x, h, matchingPartner_apply_apply M hM x⟩

#print axioms matchingPartnerFun_involutive

end Erdos19
