import ErdosProblems.Erdos73.OrderedFiniteSelection

/-! Convex spans of distinct blocks in a noncrossing port word are disjoint or nested. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Finset

variable {N : ℕ} {U : Type*}

def NoncrossingPortWord (label : Fin N → U) : Prop :=
  ∀ a b c d, a < b → b < c → c < d → label a = label c → label b = label d → label a = label b

theorem NoncrossingPortWord.interval_cases {label : Fin N → U} (h : NoncrossingPortWord label)
    {u v : U} (huv : u ≠ v) {a b c d : Fin N} (hab : a ≤ b) (hcd : c ≤ d)
    (ha : label a = u) (hb : label b = u) (hc : label c = v) (hd : label d = v) :
    b < c ∨ d < a ∨ (a < c ∧ d < b) ∨ (c < a ∧ b < d) := by
  have hac : a ≠ c := fun he => huv (ha.symm.trans ((congrArg label he).trans hc))
  have had : a ≠ d := fun he => huv (ha.symm.trans ((congrArg label he).trans hd))
  have hbc : b ≠ c := fun he => huv (hb.symm.trans ((congrArg label he).trans hc))
  have hbd : b ≠ d := fun he => huv (hb.symm.trans ((congrArg label he).trans hd))
  have hn₁ : ¬ (a < c ∧ c < b ∧ b < d) := by
    rintro ⟨h₁, h₂, h₃⟩
    exact huv (ha.symm.trans ((h a c b d h₁ h₂ h₃ (ha.trans hb.symm) (hc.trans hd.symm)).trans hc))
  have hn₂ : ¬ (c < a ∧ a < d ∧ d < b) := by
    rintro ⟨h₁, h₂, h₃⟩
    exact huv (ha.symm.trans ((h c a d b h₁ h₂ h₃ (hc.trans hd.symm) (ha.trans hb.symm)).symm.trans hc))
  omega

theorem NoncrossingPortWord.outer_block_avoids_inner {label : Fin N → U}
    (h : NoncrossingPortWord label) {u v : U} (huv : u ≠ v) {a c d : Fin N}
    (hac : a < c) (ha : label a = u) (hc : label c = v) (hd : label d = v)
    {x : Fin N} (hx : label x = u) : ¬ (c ≤ x ∧ x ≤ d) := by
  intro hbounds
  have hxc : x ≠ c := fun he => huv (hx.symm.trans ((congrArg label he).trans hc))
  have hxd : x ≠ d := fun he => huv (hx.symm.trans ((congrArg label he).trans hd))
  have hcx : c < x := by omega
  have hxd' : x < d := by omega
  exact huv (ha.symm.trans ((h a c x d hac hcx hxd' (ha.trans hx.symm) (hc.trans hd.symm)).trans hc))

def portWordFiber (label : Fin N → U) (u : U) : Finset (Fin N) := univ.filter (fun i => label i = u)

theorem mem_portWordFiber (label : Fin N → U) (u : U) (i : Fin N) :
    i ∈ portWordFiber label u ↔ label i = u := by simp only [portWordFiber, mem_filter, mem_univ, true_and]

theorem portWordFiber_nonempty (label : Fin N → U) (hsurj : Function.Surjective label) (u : U) :
    (portWordFiber label u).Nonempty := by
  obtain ⟨i, hi⟩ := hsurj u
  exact ⟨i, (mem_portWordFiber label u i).mpr hi⟩

def portWordFirst (label : Fin N → U) (hsurj : Function.Surjective label) (u : U) : Fin N :=
  (portWordFiber label u).min' (portWordFiber_nonempty label hsurj u)

def portWordLast (label : Fin N → U) (hsurj : Function.Surjective label) (u : U) : Fin N :=
  (portWordFiber label u).max' (portWordFiber_nonempty label hsurj u)

theorem portWordFirst_label (label : Fin N → U) (hsurj : Function.Surjective label) (u : U) :
    label (portWordFirst label hsurj u) = u :=
  (mem_portWordFiber _ _ _).mp (min'_mem _ _)

theorem portWordLast_label (label : Fin N → U) (hsurj : Function.Surjective label) (u : U) :
    label (portWordLast label hsurj u) = u :=
  (mem_portWordFiber _ _ _).mp (max'_mem _ _)

theorem portWord_bounds (label : Fin N → U) (hsurj : Function.Surjective label) {u : U}
    {i : Fin N} (hi : label i = u) :
    portWordFirst label hsurj u ≤ i ∧ i ≤ portWordLast label hsurj u :=
  ⟨min'_le _ _ ((mem_portWordFiber _ _ _).mpr hi),
    le_max' _ _ ((mem_portWordFiber _ _ _).mpr hi)⟩

theorem portWordFirst_le_last (label : Fin N → U) (hsurj : Function.Surjective label) (u : U) :
    portWordFirst label hsurj u ≤ portWordLast label hsurj u :=
  (portWord_bounds label hsurj (portWordFirst_label label hsurj u)).2

def portWordSpine (label : Fin N → U) (hsurj : Function.Surjective label) (u : U) : ℕ :=
  (portWordLast label hsurj u).val - (portWordFirst label hsurj u).val + 1

theorem portWordSpine_pos (label : Fin N → U) (hsurj : Function.Surjective label) (u : U) :
    0 < portWordSpine label hsurj u := by dsimp only [portWordSpine]; omega

theorem portWordSpine_le (label : Fin N → U) (hsurj : Function.Surjective label) (u : U) :
    portWordSpine label hsurj u ≤ N := by
  have hh := (portWordLast label hsurj u).isLt
  dsimp only [portWordSpine]
  omega

theorem portWordSpine_lt_of_nested (label : Fin N → U) (hsurj : Function.Surjective label)
    {u v : U} (hlo : portWordFirst label hsurj u < portWordFirst label hsurj v)
    (hhi : portWordLast label hsurj v < portWordLast label hsurj u) :
    portWordSpine label hsurj v < portWordSpine label hsurj u := by
  have hu := portWordFirst_le_last label hsurj u
  have hv := portWordFirst_le_last label hsurj v
  dsimp only [portWordSpine]
  omega

end
end Erdos73
