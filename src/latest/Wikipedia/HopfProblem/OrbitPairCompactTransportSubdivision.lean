import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Maps.Proper.Basic
import Wikipedia.NoExoticSixSphere.CompactParameter

/-!
# Uniform time subdivisions for compact families and open diagonal relations

An open relation containing the diagonal need not come from a metric.
Compactness of the parameter space gives a subdivision on which every
pair of times in one step satisfies that relation, uniformly in the
parameter. This is the topological input for local fibre transport.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.OrbitPair

variable {B X : Type*} [TopologicalSpace B] [TopologicalSpace X] [CompactSpace X]

theorem exists_compact_transport_subdivision (H : C(I × X, B))
    (W : Set (B × B)) (hW : IsOpen W) (hdiag : ∀ b, (b, b) ∈ W) :
    ∃ t : ℕ → I, t 0 = 0 ∧ Monotone t ∧ (∃ N, ∀ i ≥ N, t i = 1) ∧
      ∀ i, ∀ u ∈ Icc (t i) (t (i + 1)), ∀ x,
        (H (t i, x), H (u, x)) ∈ W := by
  let V : Set (I × I) := {s | ∀ x, (H (s.1, x), H (s.2, x)) ∈ W}
  have hV : IsOpen V := by
    have h₁ : Continuous (fun p : (I × I) × X => H (p.1.1, p.2)) :=
      H.continuous.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
    have h₂ : Continuous (fun p : (I × I) × X => H (p.1.2, p.2)) :=
      H.continuous.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
    exact NoExoticSixSphere.isOpen_forall_compact (hW.preimage (h₁.prodMk h₂))
  have hlocal : ∀ s : I, ∃ U : Set I, IsOpen U ∧ s ∈ U ∧ U ×ˢ U ⊆ V := by
    intro s
    have hs : (s, s) ∈ V := fun x => hdiag (H (s, x))
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp (hV.mem_nhds hs)
    obtain ⟨U, hUsub, hUopen, hsU⟩ := mem_nhds_iff.mp (Filter.inter_mem hu hv)
    exact ⟨U, hUopen, hsU, fun z hz => huv ⟨(hUsub hz.1).1, (hUsub hz.2).2⟩⟩
  choose U hU hsU hUU using hlocal
  obtain ⟨t, ht₀, hmono, hend, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hU
      (fun s _ => mem_iUnion.mpr ⟨s, hsU s⟩)
  refine ⟨t, ht₀, hmono, hend, ?_⟩
  intro i u hu x
  obtain ⟨s, hs⟩ := hsub i
  have hpair : (t i, u) ∈ V :=
    hUU s ⟨hs ⟨le_rfl, hmono i.le_succ⟩, hs hu⟩
  exact hpair x

end Wikipedia.HopfProblem.OrbitPair
