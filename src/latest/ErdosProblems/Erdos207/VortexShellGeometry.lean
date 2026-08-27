/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.StructuredInitialData
import ErdosProblems.Erdos207.ReserveProtectedPreliminaryGeometry
import ErdosProblems.Erdos207.CliquePatternTypicality

/-! # Exact future-prefix levels of protected triangles -/

namespace Erdos207

open Finset

noncomputable section

theorem TrianglesMeetAtMostOne.not_subset
    {V : Type*} [DecidableEq V] {U : Finset V} {A : TripleSystemOn V}
    (hA : TrianglesMeetAtMostOne U A) {T : TripleOn V} (hT : T ∈ A) : ¬ T.1 ⊆ U := by
  intro hsub
  obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.mp (show 1 < T.1.card by rw [T.2]; decide)
  exact hxy (hA T hT hx (hsub hx) hy (hsub hy))

theorem reserveProtectedOuterAvailable_shell
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (D U : Finset V) (R : Finset (Sym2 V)) (A : TripleSystemOn V)
    (hG : GraphSupportedOn G (D : Set V))
    (hA : ∀ T ∈ A, tripleEdgeFinset T ⊆ graphEdges G) :
    ∀ T ∈ reserveProtectedOuterAvailable G U R A, T.1 ⊆ D ∧ ¬ T.1 ⊆ U := by
  intro T hT
  exact ⟨triple_supported_of_graph_edges G D T hG
    (hA T (reserveProtectedOuterAvailable_subset G U R A hT)),
    (trianglesMeetAtMostOne_reserveProtectedOuterAvailable G U R A).not_subset hT⟩

theorem Vortex.prefix_level_eq_last_of_subset
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1)) (T : TripleOn V) (hT : T.1 ⊆ W.U k) :
    (W.prefix k).level T = Fin.last k.val := by
  apply le_antisymm (Fin.le_last _)
  apply (W.prefix k).le_level_of_subset T
  simpa only [prefix_U, vortexPrefixEmbedding_last] using hT

theorem Vortex.prefix_level_eq_of_shell
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin ell) (m : Fin (ell + 1)) (hkm : k.val < m.val)
    (T : TripleOn V) (hT : T.1 ⊆ W.U k.castSucc) (hnext : ¬ T.1 ⊆ W.U k.succ) :
    (W.prefix m).level T = (⟨k.val, hkm⟩ : Fin m.val).castSucc := by
  have hemb : vortexPrefixEmbedding m (⟨k.val, hkm⟩ : Fin m.val).castSucc = k.castSucc := by
    apply Fin.ext
    rfl
  apply le_antisymm
  · by_contra hle
    have hlt := lt_of_not_ge hle
    have hnextle : k.succ ≤ vortexPrefixEmbedding m ((W.prefix m).level T) := by
      change k.val + 1 ≤ ((W.prefix m).level T).val
      change k.val < ((W.prefix m).level T).val at hlt
      omega
    exact hnext (((W.prefix m).subset_at_level T).trans
      (W.antitone k.succ (vortexPrefixEmbedding m ((W.prefix m).level T)) hnextle))
  · apply (W.prefix m).le_level_of_subset T
    simpa only [prefix_U, hemb] using hT

theorem Vortex.prefix_outer_level_terminal_in_shorter
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin ell) (m : Fin (ell + 1)) (hkm : k.val < m.val)
    (T : TripleOn V) (hlevel : (W.prefix m).level T = (⟨k.val, hkm⟩ : Fin m.val).castSucc) :
    (W.prefix k.castSucc).level T = Fin.last k.val := by
  apply W.prefix_level_eq_last_of_subset k.castSucc T
  have hsub := (W.prefix m).subset_at_level T
  rw [hlevel, prefix_U] at hsub
  have hemb : vortexPrefixEmbedding m (⟨k.val, hkm⟩ : Fin m.val).castSucc = k.castSucc := by
    apply Fin.ext
    rfl
  simpa only [hemb] using hsub

theorem Vortex.prefix_outer_level_size
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin ell) (m : Fin (ell + 1)) (hkm : k.val < m.val) :
    (W.prefix k.castSucc).terminalSize =
      ((W.prefix m).U (⟨k.val, hkm⟩ : Fin m.val).castSucc).card := by
  rw [prefix_terminalSize, prefix_U]
  congr 2

end

end Erdos207
