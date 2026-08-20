import ErdosProblems.Erdos733.ST.Preamble
import Mathlib.Topology.Order.Compact

open Classical
noncomputable section

-- [TABLET NODE: PositiveSeparation]
lemma PositiveSeparation {A B : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : A.Nonempty) (hB : B.Nonempty) (hAc : IsCompact A) (hBc : IsCompact B)
    (hdisj : Disjoint A B) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a, a ∈ A → ∀ b, b ∈ B → δ ≤ dist a b := by
-- BODY
  let s : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) := A ×ˢ B
  have hs_nonempty : s.Nonempty := by
    rcases hA with ⟨a, ha⟩
    rcases hB with ⟨b, hb⟩
    exact ⟨(a, b), ⟨ha, hb⟩⟩
  have hs_compact : IsCompact s := hAc.prod hBc
  have hdist_cont : ContinuousOn (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      dist p.1 p.2) s := continuous_fst.dist continuous_snd |>.continuousOn
  have hdist_pos : ∀ p ∈ s, (0 : ℝ) < dist p.1 p.2 := by
    intro p hp
    rw [dist_pos]
    intro hp_eq
    have hpB : p.1 ∈ B := by
      simpa [hp_eq] using hp.2
    exact Set.disjoint_left.mp hdisj hp.1 hpB
  obtain ⟨p, hp, hp_min⟩ :=
    hs_compact.exists_isMinOn hs_nonempty hdist_cont
  exact ⟨dist p.1 p.2, hdist_pos p hp,
    fun a ha b hb => (isMinOn_iff.mp hp_min) (a, b) ⟨ha, hb⟩⟩
