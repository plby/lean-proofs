-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.E5CountableReduction

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite-colour-bound formulations of the remaining E5 input

The contrapositive form of the Hajnal--Komjáth result says that a linear triple
system omitting the loose seven-cycle has bounded weak chromatic number.  This
file isolates both the uniform and nonuniform versions of that assertion and
proves their precise connections to the E5 interface.
-/

open Cardinal

namespace Erdos1177

universe u

/-- Every linear loose-seven-cycle-free triple system is finitely weakly
colourable (with a bound allowed to depend on the system). -/
def Loose7FreeFinitelyColorable : Prop :=
  ∀ {W : Type u} (H : Hypergraph W), H.IsTripleSystem → H.Linear →
    ¬ looseCycle7.Embeds H →
    ∃ k : ℕ, 0 < k ∧ ∃ c : W → Fin k, H.ProperColoring c

/-- Uniform finite-bound form: one finite palette works for every linear
loose-seven-cycle-free triple system. -/
def Loose7FreeUniformFiniteBound : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∀ {W : Type u} (H : Hypergraph W),
    H.IsTripleSystem → H.Linear → ¬ looseCycle7.Embeds H →
    ∃ c : W → Fin k, H.ProperColoring c

/-
A uniform finite bound implies the nonuniform finite-colourability form.
-/
theorem loose7Free_finitelyColorable_of_uniformFiniteBound
    (h : Loose7FreeUniformFiniteBound.{u}) :
    Loose7FreeFinitelyColorable.{u} := by
  intro W H htri hlin hno;
  exact ⟨ h.choose, h.choose_spec.1, h.choose_spec.2 H htri hlin hno ⟩

/-
The nonuniform contrapositive already implies the E5 conclusion: an
uncountably chromatic host cannot admit any finite proper colouring.
-/
theorem e5_HK_loose7_of_loose7Free_finitelyColorable
    (h : Loose7FreeFinitelyColorable.{u}) : E5_HK_loose7.{u} := by
  contrapose! h;
  contrapose! h with h_contra;
  apply e5_HK_loose7_of_countable_embedding_principle;
  intro W H A htri hlin hcount hsub huc;
  apply Classical.byContradiction
  intro h_no_embedding;
  exact huc ( Classical.choose ( h_contra ⟨ A ⟩ ( isTripleSystem_of_edges_subset H htri A hsub ) ( linear_of_edges_subset H hlin A hsub ) h_no_embedding ) ) ( Classical.choose_spec ( h_contra ⟨ A ⟩ ( isTripleSystem_of_edges_subset H htri A hsub ) ( linear_of_edges_subset H hlin A hsub ) h_no_embedding ) |>.1 ) ( Classical.choose_spec ( h_contra ⟨ A ⟩ ( isTripleSystem_of_edges_subset H htri A hsub ) ( linear_of_edges_subset H hlin A hsub ) h_no_embedding ) |>.2 )

/-
Hence a uniform Hajnal--Komjáth finite-colour bound implies E5.
-/
theorem e5_HK_loose7_of_uniformFiniteBound
    (h : Loose7FreeUniformFiniteBound.{u}) : E5_HK_loose7.{u} := by
  obtain ⟨ k, hk, hk ⟩ := h;
  apply e5_HK_loose7_of_loose7Free_finitelyColorable;
  intro W H htri hlin hloose;
  exact ⟨ k, by assumption, hk H htri hlin hloose ⟩

/-
The nonuniform finite-colourability theorem directly yields the countable
embedding principle isolated in `E5CountableReduction`.
-/
theorem countableEmbeddingPrinciple_of_loose7Free_finitelyColorable
    (h : Loose7FreeFinitelyColorable.{u}) :
    E5CountableEmbeddingPrinciple.{u} := by
  intro W H A htri hlin hAcount hAsub hunbounded; contrapose! hunbounded;
  convert! h ⟨ A ⟩ ( isTripleSystem_of_edges_subset H htri A hAsub ) ( linear_of_edges_subset H hlin A hAsub ) hunbounded

/-
The uniform bound yields the countable-core principle as well.
-/
theorem countableEmbeddingPrinciple_of_uniformFiniteBound
    (h : Loose7FreeUniformFiniteBound.{u}) :
    E5CountableEmbeddingPrinciple.{u} := by
  exact countableEmbeddingPrinciple_of_loose7Free_finitelyColorable ( loose7Free_finitelyColorable_of_uniformFiniteBound h )

/-- A host-specific finite bound is sufficient: if every loose-seven-free
linear triple system in the universe is `k`-colourable, then every linear host
which is not `k`-colourable contains the loose cycle. -/
theorem looseCycle7_embeds_of_not_colorable_bound
    (k : ℕ)
    (hbound : ∀ {W : Type u} (K : Hypergraph W),
      K.IsTripleSystem → K.Linear → ¬ looseCycle7.Embeds K →
      ∃ c : W → Fin k, K.ProperColoring c)
    {W : Type u} (H : Hypergraph W) (htri : H.IsTripleSystem)
    (hlin : H.Linear)
    (hncol : ¬ ∃ c : W → Fin k, H.ProperColoring c) :
    looseCycle7.Embeds H := by
  exact Classical.not_not.1 fun h => hncol <| hbound H htri hlin h

end Erdos1177
