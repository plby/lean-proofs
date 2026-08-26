import ErdosProblems.Erdos547.RegularityManyTypical

/-!
# Upper bounds for typical degrees in regular pairs
-/

namespace Erdos547

open Finset SimpleGraph
open scoped BigOperators

variable {V I : Type*}

open scoped Classical in
theorem card_upper_nonTypical_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {S T B : Finset V} {ε : ℝ}
    (hreg : G.IsUniform ε S T) (hB : B ⊆ T) (hsize : (T.card : ℝ) * ε ≤ B.card) :
    ((S.filter (fun u ↦ ((G.edgeDensity S T : ℝ) + ε) * B.card <
      (degreeIn G B u : ℝ))).card : ℝ) ≤ (S.card : ℝ) * ε := by
  classical
  let bad := S.filter (fun u ↦ ((G.edgeDensity S T : ℝ) + ε) * B.card <
    (degreeIn G B u : ℝ))
  change (bad.card : ℝ) ≤ (S.card : ℝ) * ε
  by_contra hn
  have hbad : (S.card : ℝ) * ε < (bad.card : ℝ) := lt_of_not_ge hn
  have hbpos : 0 < bad.card := by
    exact_mod_cast (mul_nonneg (Nat.cast_nonneg S.card) hreg.pos.le).trans_lt hbad
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hbpos
  have hBne : B.Nonempty := by
    by_contra hne
    have hz : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hh := (Finset.mem_filter.mp hu).2
    simp only [hz, degreeIn, Finset.filter_empty, Finset.card_empty, Nat.cast_zero,
      mul_zero, lt_self_iff_false] at hh
  have hden : 0 < (bad.card : ℝ) * B.card :=
    mul_pos (by exact_mod_cast hbpos) (by exact_mod_cast hBne.card_pos)
  have hs : (∑ _z ∈ bad, (((G.edgeDensity S T : ℝ) + ε) * B.card)) <
      ∑ z ∈ bad, (degreeIn G B z : ℝ) :=
    Finset.sum_lt_sum (fun z hz ↦ (Finset.mem_filter.mp hz).2.le)
      ⟨u, hu, (Finset.mem_filter.mp hu).2⟩
  have hdensity : (G.edgeDensity S T : ℝ) + ε < (G.edgeDensity bad B : ℝ) := by
    rw [edgeDensity_eq_sum_degreeIn_div G bad B]
    apply (lt_div_iff₀ hden).mpr
    simp only [Finset.sum_const, nsmul_eq_mul] at hs
    nlinarith only [hs]
  have hregular := hreg (Finset.filter_subset _ _) hB hbad.le hsize
  have hh := (abs_lt.mp hregular).2
  linarith

open scoped Classical in
theorem card_many_upper_nonTypical_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (J : Finset I) (T B : I → Finset V) (ε δ : ℝ)
    (hδ : 0 < δ) (hεδ : ε ≤ δ ^ 2)
    (hreg : ∀ i ∈ J, G.IsUniform ε S (T i))
    (hB : ∀ i ∈ J, B i ⊆ T i)
    (hsize : ∀ i ∈ J, ((T i).card : ℝ) * ε ≤ (B i).card) :
    ((S.filter (fun u ↦ δ * J.card < ((J.filter (fun i ↦
      ((G.edgeDensity S (T i) : ℝ) + ε) * (B i).card <
        (degreeIn G (B i) u : ℝ))).card : ℝ))).card : ℝ)
      ≤ δ * S.card := by
  classical
  apply card_many_incidents_le _ S J ε δ hδ hεδ
  intro i hi
  simpa only [mul_comm ε] using card_upper_nonTypical_le G (hreg i hi) (hB i hi) (hsize i hi)

end Erdos547

#print axioms Erdos547.card_upper_nonTypical_le
#print axioms Erdos547.card_many_upper_nonTypical_le
