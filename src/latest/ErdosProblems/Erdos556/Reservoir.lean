import ErdosProblems.Erdos556.DeletionPaths
import ErdosProblems.Erdos556.ResilientSampling

/-!
# Connecting reservoirs

The theorem in this file constructs a small set which contains the internal
vertices of a short path between every two vertices, even after a bounded
number of reservoir vertices are forbidden. All finite size and failure
inequalities are explicit.
-/

namespace Erdos556

open SimpleGraph Finset

/-- A short path whose internal vertices lie in the specified set. -/
def ShortConnection {V : Type*} (G : SimpleGraph V) (L : ℕ) (u v : V)
    (S : Finset V) : Prop :=
  ∃ p : G.Walk u v, p.IsPath ∧ p.length ≤ L ∧
    ∀ x ∈ p.support, x ≠ u → x ≠ v → x ∈ S

theorem ShortConnection.mono {V : Type*} {G : SimpleGraph V} {L : ℕ} {u v : V}
    {S T : Finset V} (h : ShortConnection G L u v S) (hST : S ⊆ T) :
    ShortConnection G L u v T := by
  obtain ⟨p, hp, hlen, hs⟩ := h
  exact ⟨p, hp, hlen, fun x hx hxu hxv => hST (hs x hx hxu hxv)⟩

theorem exists_short_connection_avoiding {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b d L : ℕ)
    (hconn : ConnectedAfterDeleting G b) (hd : 0 < d)
    (hdeg : ∀ w, d + b ≤ G.degree w) (hdiam : 3 * Fintype.card V ≤ d * L)
    (u v : V) (S : Finset V) (hS : S.card ≤ b) :
    ∃ T : Finset V, ShortConnection G L u v T ∧ T.card ≤ L ∧ Disjoint S T := by
  classical
  let S' := (S.erase u).erase v
  have hS' : S'.card ≤ b :=
    (Finset.card_le_card ((erase_subset v (S.erase u)).trans (erase_subset u S))).trans hS
  obtain ⟨p, hp, hlen, hav⟩ := exists_short_path_avoiding G b d hconn hd hdeg S' hS'
    u v (by simp [S']) (by simp [S'])
  have hlen' : p.length + 1 ≤ L := by nlinarith
  let T := (p.support.toFinset.erase u).erase v
  refine ⟨T, ⟨p, hp, by omega, ?_⟩, ?_, ?_⟩
  · intro x hx hxu hxv
    simp only [T, mem_erase, List.mem_toFinset]
    exact ⟨hxv, hxu, hx⟩
  · calc
      T.card ≤ p.support.toFinset.card :=
        Finset.card_le_card ((erase_subset v _).trans (erase_subset u _))
      _ ≤ p.support.length := List.toFinset_card_le p.support
      _ = p.length + 1 := p.length_support
      _ ≤ L := hlen'
  · rw [Finset.disjoint_left]
    intro x hxS hxT
    simp only [T, mem_erase, List.mem_toFinset] at hxT
    apply hav x hxT.2.2
    simp only [S', mem_erase]
    exact ⟨hxT.1, hxT.2.1, hxS⟩

/-- A finite connecting-reservoir theorem, with an explicit sampling bound. -/
theorem exists_connecting_reservoir {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b d L m a : ℕ)
    (hconn : ConnectedAfterDeleting G b) (hd : 0 < d)
    (hdeg : ∀ w, d + b ≤ G.degree w) (hdiam : 3 * Fintype.card V ≤ d * L)
    (hbound : ((a + 1) * m) * L ≤ b)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hfail : (Fintype.card V : ℝ) ^ 2 * (a + 1) * (1 - q ^ L) ^ m < 1 / 2)
    (hV : 0 < Fintype.card V) :
    ∃ R : Finset V, (R.card : ℝ) ≤ 2 * q * Fintype.card V ∧
      ∀ u v S, S.card ≤ a → ShortConnection G L u v (R \ S) := by
  classical
  let P : (V × V) → Finset V → Prop := fun uv => ShortConnection G L uv.1 uv.2
  have hav (uv : V × V) (S : Finset V) (hS : S.card ≤ b) :
      ∃ T : Finset V, P uv T ∧ T.card ≤ L ∧ Disjoint S T :=
    exists_short_connection_avoiding G b d L hconn hd hdeg hdiam uv.1 uv.2 S hS
  have hf : (Fintype.card (V × V) : ℝ) * (a + 1) *
      (1 - q ^ L) ^ m < 1 / 2 := by
    simpa only [Fintype.card_prod, Nat.cast_mul, pow_two] using hfail
  obtain ⟨R, hR, hhit⟩ := exists_small_set_of_avoidance P q hq0 hq1 L b m a
    hbound hav hf hV
  refine ⟨R, hR, ?_⟩
  intro u v S hS
  obtain ⟨T, hTR, hP, _, hST⟩ := hhit (u, v) S hS
  apply hP.mono
  intro x hx
  exact mem_sdiff.mpr ⟨hTR hx, fun hxS => Finset.disjoint_left.mp hST hxS hx⟩

#print axioms exists_connecting_reservoir

end Erdos556
