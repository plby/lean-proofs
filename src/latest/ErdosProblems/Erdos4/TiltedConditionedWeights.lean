import ErdosProblems.Erdos4.TiltedMoments

/-! Conditioning identities for the normalized root incidence and the lost cap mass. -/

namespace Erdos4.Tilted

open FGKMT

variable {Ω I : Type*} [Fintype Ω] [Fintype I]

theorem condition_eventWeight (ν : FiniteLaw Ω) (E R : Ω → Prop) [DecidablePred R]
    (o₀ : Ω) (hR : ν.prob R ≠ 0) (hER : ∀ o, E o → R o) (o : Ω) :
    eventWeight (ν.condition R o₀) E o = ν.prob R * eventWeight ν E o := by
  classical
  have heq : (fun o => R o ∧ E o) = E := by
    funext o
    exact propext ⟨And.right, fun h => ⟨hER o h, h⟩⟩
  have hp : (ν.condition R o₀).prob E = ν.prob E / ν.prob R := by
    rw [FiniteLaw.condition_prob _ _ _ _ hR, heq]
  unfold eventWeight
  rw [hp]
  by_cases he : E o
  · simp only [if_pos he, div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  · simp [he]

theorem condition_eventNormalizer (ν : FiniteLaw Ω) (σ : FiniteLaw I)
    (E : I → Ω → Prop) (R : Ω → Prop) [DecidablePred R]
    (o₀ : Ω) (hR : ν.prob R ≠ 0) (hER : ∀ i o, E i o → R o) (o : Ω) :
    eventNormalizer (ν.condition R o₀) σ E o = ν.prob R * eventNormalizer ν σ E o := by
  unfold eventNormalizer
  calc
    _ = σ.mean (fun i => ν.prob R * eventWeight ν (E i) o) :=
      σ.mean_congr (fun i => condition_eventWeight ν (E i) R o₀ hR (hER i) o)
    _ = _ := σ.mean_const_mul _ _

theorem condition_normalizer_variance_eq (ν : FiniteLaw Ω) (σ : FiniteLaw I)
    (E F : I → Ω → Prop) (R : Ω → Prop) [DecidablePred R]
    (o₀ : Ω) (hR : ν.prob R ≠ 0) (hE : ∀ i o, E i o ↔ R o ∧ F i o) :
    (ν.condition R o₀).mean (fun o => (ν.prob R * eventNormalizer ν σ E o - 1) ^ 2) =
      (ν.condition R o₀).mean (fun o => (eventNormalizer (ν.condition R o₀) σ F o - 1) ^ 2) := by
  classical
  have hprob (i : I) : (ν.condition R o₀).prob (E i) = (ν.condition R o₀).prob (F i) := by
    rw [FiniteLaw.condition_prob _ _ _ _ hR, FiniteLaw.condition_prob _ _ _ _ hR]
    congr 2
    funext o
    exact propext ⟨fun h => ⟨h.1, ((hE i o).mp h.2).2⟩,
      fun h => ⟨h.1, (hE i o).mpr h⟩⟩
  apply (ν.condition R o₀).mean_congr_support
  intro o ho
  have hRo := FiniteLaw.condition_support ν R o₀ o hR ho
  have hnormal : eventNormalizer (ν.condition R o₀) σ E o =
      eventNormalizer (ν.condition R o₀) σ F o := by
    apply σ.mean_congr
    intro i
    have hei : E i o ↔ F i o := by simpa only [hRo, true_and] using hE i o
    simp only [eventWeight, hei, hprob i]
  rw [← condition_eventNormalizer ν σ E R o₀ hR (fun i o h => ((hE i o).mp h).1), hnormal]

theorem mean_on_event_eq_condition (ν : FiniteLaw Ω) (R : Ω → Prop) [DecidablePred R]
    (o₀ : Ω) (hR : ν.prob R ≠ 0) (f : Ω → ℝ) :
    ν.mean (fun o => if R o then f o else 0) = ν.prob R * (ν.condition R o₀).mean f := by
  rw [FiniteLaw.condition_mean _ _ _ hR]
  field_simp

theorem condition_mean_mul_eq (ν : FiniteLaw Ω) (R : Ω → Prop) [DecidablePred R]
    (o₀ : Ω) (hR : ν.prob R ≠ 0) (f : Ω → ℝ) (hsupport : ∀ o, ¬R o → f o = 0) :
    ν.prob R * (ν.condition R o₀).mean f = ν.mean f := by
  rw [← mean_on_event_eq_condition ν R o₀ hR f]
  apply ν.mean_congr
  intro o
  by_cases ho : R o
  · simp [ho]
  · simp [ho, hsupport o ho]

end Erdos4.Tilted
