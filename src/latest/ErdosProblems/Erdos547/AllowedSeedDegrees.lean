import ErdosProblems.Erdos547.AllowedShrubHeads
import ErdosProblems.Erdos547.SeedTypicalPools

/-!
# Every attachment has the required degree into an allowed head
-/

namespace Erdos547

open Finset SimpleGraph

theorem degreeIn_of_not_exceptional_partner {V I : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ) (X : Finset V) (J : Finset I)
    (C B : I → Finset V) (v : V) (i : I) (hi : i ∈ J)
    (hgood : i ∉ nonTypicalPartners G ε X J C B v) :
    ((G.edgeDensity X (C i) : ℝ) - ε) * (B i).card ≤ (degreeIn G (B i) v : ℝ) := by
  apply le_of_not_gt
  intro hh
  exact hgood (Finset.mem_filter.mpr ⟨hi, hh⟩)

namespace FineTreePartition

variable {U V I : Type*} [Fintype U] [DecidableEq U] [DecidableEq V]
  [Fintype I] [DecidableEq I] {T : SimpleGraph U} [DecidableRel T.Adj]
  {r : U} {ℓ : ℕ} {col : T.Coloring (Fin 2)} (P : FineTreePartition T r ℓ col)

noncomputable def seedExceptions (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (X : Fin 2 → Finset V) (J : Fin 2 → Finset I) (C B : I → Finset V)
    (seed : ↥P.seeds → V) (z : ↥P.seeds) : Finset I :=
  nonTypicalPartners G ε (X (col z.val)) (J (col z.val)) C B (seed z)

theorem allowed_attachment_degrees (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε θ : ℝ) (X : Fin 2 → Finset V) (J : Fin 2 → Finset I) (C B Q : I → Finset V)
    (seed : ↥P.seeds → V) (anchors : Finset I) (w : Fin 2 → I → ℝ)
    (hsupport : ∀ c i, θ ≤ w c i → i ∈ J c) (S : ↥P.shrubs) (i : I)
    (hi : i ∈ P.allowedHeads anchors (P.seedExceptions G ε X J C B seed)
      (P.seedExceptions G ε X J C Q seed) w θ S)
    (z : ↥P.seeds) (hz : z ∈ P.attachmentSeeds S) :
    ((G.edgeDensity (X (P.shrubColour S)) (C i) : ℝ) - ε) * (B i).card ≤
      (degreeIn G (B i) (seed z) : ℝ) ∧
    ((G.edgeDensity (X (P.shrubColour S)) (C i) : ℝ) - ε) * (Q i).card ≤
      (degreeIn G (Q i) (seed z) : ℝ) := by
  have hp := P.allowedHeads_properties anchors (P.seedExceptions G ε X J C B seed)
    (P.seedExceptions G ε X J C Q seed) w θ S i hi
  have hc := P.attachmentSeeds_colour S z hz
  have hJ : i ∈ J (col z.val) := by
    rw [hc]
    exact hsupport _ i hp.1
  have hB := degreeIn_of_not_exceptional_partner G ε (X (col z.val)) (J (col z.val)) C B
    (seed z) i hJ (hp.2.2 z hz).1
  have hQ := degreeIn_of_not_exceptional_partner G ε (X (col z.val)) (J (col z.val)) C Q
    (seed z) i hJ (hp.2.2 z hz).2
  rw [hc] at hB hQ
  exact ⟨hB, hQ⟩

theorem seedExceptions_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε δ : ℝ) (hδ : 0 ≤ δ) (X : Fin 2 → Finset V) (J : Fin 2 → Finset I)
    (C B : I → Finset V) (seed : ↥P.seeds → V)
    (htypical : ∀ z, ((P.seedExceptions G ε X J C B seed z).card : ℝ) ≤ δ * (J (col z.val)).card)
    (z : ↥P.seeds) : ((P.seedExceptions G ε X J C B seed z).card : ℝ) ≤ δ * Fintype.card I :=
  (htypical z).trans (mul_le_mul_of_nonneg_left
    (by exact_mod_cast Finset.card_le_univ (J (col z.val))) hδ)

end FineTreePartition
end Erdos547

#print axioms Erdos547.FineTreePartition.allowed_attachment_degrees
