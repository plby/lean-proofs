import Arxiv.Arxiv2407_19026.BookCor

/-!
# Optimizing descent to a candidate

This file formalizes the discrete descent mechanism in Section 4.  The
paper's compactness and computer-verified analytic inputs are represented
by explicit certificate structures; the combinatorial induction below
checks those inputs without adding axioms.
-/

noncomputable section

open Finset

namespace Arxiv2407_19026

/-- Uniform meaning of `R(k,l) ≤ exp(F(l/k) k + o(k))` in the range
`1 ≤ l ≤ k`. -/
def HasRamseyExponent (F : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ K : ℕ, ∀ k l : ℕ, K ≤ k → 1 ≤ l → l ≤ k →
      (ramseyNumber k l : ℝ) ≤
        Real.exp ((F ((l : ℝ) / k) + ε) * k)

/-- Integer threshold corresponding to equation `e:epsBound`. -/
def exponentThreshold (F : ℝ → ℝ) (ε : ℝ) (k l : ℕ) : ℕ :=
  ⌊Real.exp ((F ((l : ℝ) / k) + ε) * k)⌋₊

lemma exponentThreshold_le_exp (F : ℝ → ℝ) (ε : ℝ) (k l : ℕ) :
    (exponentThreshold F ε k l : ℝ) ≤
      Real.exp ((F ((l : ℝ) / k) + ε) * k) := by
  exact Nat.floor_le (Real.exp_nonneg _)

lemma sum_blueDegrees_add_redEdges {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    (∑ v : V, (blueNeighborsIn G v Finset.univ).card) +
        redEdgesBetween G Finset.univ Finset.univ =
      Fintype.card V * (Fintype.card V - 1) := by
  have hpoint :
      ∀ v : V,
        (blueNeighborsIn G v Finset.univ).card +
            (redNeighborsIn G v Finset.univ).card =
          Fintype.card V - 1 := by
    intro v
    have h := card_redNeighbors_add_card_blueNeighbors G v
    omega
  calc
    (∑ v : V, (blueNeighborsIn G v Finset.univ).card) +
          redEdgesBetween G Finset.univ Finset.univ =
        ∑ v : V,
          ((blueNeighborsIn G v Finset.univ).card +
            (redNeighborsIn G v Finset.univ).card) := by
      rw [redEdgesBetween_eq_sum_card]
      simp [sum_add_distrib]
    _ = ∑ _v : V, (Fintype.card V - 1) := by
      apply Finset.sum_congr rfl
      intro v _
      exact hpoint v
    _ = Fintype.card V * (Fintype.card V - 1) := by
      simp [mul_comm]

/-- If the red density is below `p`, some vertex has more than the
complementary average blue degree. -/
lemma exists_large_blueDegree_of_globalRedDensity_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {p : ℝ}
    (hn : 2 ≤ Fintype.card V)
    (hp : globalRedDensity G < p) :
    ∃ v : V,
      (1 - p) * (Fintype.card V - 1) <
        (blueNeighborsIn G v Finset.univ).card := by
  let n := Fintype.card V
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) * (n - 1) := by
    have : 0 < (n : ℝ) - 1 := by linarith
    positivity
  have hred :
      (redEdgesBetween G Finset.univ Finset.univ : ℝ) <
        p * (n : ℝ) * (n - 1) := by
    have hp' :
        (redEdgesBetween G Finset.univ Finset.univ : ℝ) /
            ((n : ℝ) * (n - 1)) < p := by
      simpa [globalRedDensity, n] using hp
    simpa [mul_assoc] using (div_lt_iff₀ hden).1 hp'
  by_contra hnone
  push Not at hnone
  have hsumBlue :
      (∑ v : V, ((blueNeighborsIn G v Finset.univ).card : ℝ)) ≤
        (n : ℝ) * ((1 - p) * (n - 1)) := by
    calc
      (∑ v : V, ((blueNeighborsIn G v Finset.univ).card : ℝ)) ≤
          ∑ _v : V, (1 - p) * (n - 1) := by
        exact Finset.sum_le_sum fun v _ ↦ hnone v
      _ = (n : ℝ) * ((1 - p) * (n - 1)) := by
        simp [n, mul_comm]
  have hidentity :
      (∑ v : V, ((blueNeighborsIn G v Finset.univ).card : ℝ)) +
          redEdgesBetween G Finset.univ Finset.univ =
        (n : ℝ) * (n - 1) := by
    have hNat := congrArg (fun z : ℕ ↦ (z : ℝ))
      (sum_blueDegrees_add_redEdges G)
    simpa [n, Nat.cast_sub (by omega : 1 ≤ n)] using hNat
  nlinarith

/-- Data needed for one fully uniform application of the descent
argument. `active k l` is the range handled by the dense book branch;
the complementary range is supplied by `base`. -/
structure DescentCertificate
    (F : ℝ → ℝ) (ε : ℝ) where
  active : ℕ → ℕ → Prop
  p : ℕ → ℕ → ℝ
  cutoff : ℕ
  active_two :
    ∀ k l, cutoff ≤ k → 1 ≤ l → l ≤ k →
      active k l → 2 ≤ l
  threshold_two :
    ∀ k l, cutoff ≤ k → 1 ≤ l → l ≤ k →
      active k l → 2 ≤ exponentThreshold F ε k l
  p_bounds :
    ∀ k l, cutoff ≤ k → 1 ≤ l → l ≤ k →
      active k l → 0 < p k l ∧ p k l < 1
  base :
    ∀ k l, cutoff ≤ k → 1 ≤ l → l ≤ k →
      ¬active k l →
      RamseyProperty k l (exponentThreshold F ε k l)
  dense :
    ∀ k l, cutoff ≤ k → 1 ≤ l → l ≤ k →
      active k l →
      ∀ G : SimpleGraph (Fin (exponentThreshold F ε k l)),
        p k l ≤ globalRedDensity G →
        ¬(G.CliqueFree k ∧ G.IndepSetFree l)
  blue_step :
    ∀ k l, cutoff ≤ k → 1 ≤ l → l ≤ k →
      active k l →
      (exponentThreshold F ε k (l - 1) : ℝ) ≤
        (1 - p k l) *
          (exponentThreshold F ε k l - 1)

/-- The certified form of the induction in Theorem `t:general`. -/
theorem ramseyProperty_exponentThreshold_of_certificate
    {F : ℝ → ℝ} {ε : ℝ}
    (C : DescentCertificate F ε) :
    ∀ k l : ℕ, C.cutoff ≤ k → 1 ≤ l → l ≤ k →
      RamseyProperty k l (exponentThreshold F ε k l) := by
  intro k
  intro l
  induction l using Nat.strong_induction_on with
  | h l ih =>
      intro hk hl hlk
      by_cases hactive : C.active k l
      · intro G hbad
        by_cases hdense : C.p k l ≤ globalRedDensity G
        · exact C.dense k l hk hl hlk hactive G hdense hbad
        · have hlt : globalRedDensity G < C.p k l :=
            lt_of_not_ge hdense
          have hn :
              2 ≤ exponentThreshold F ε k l :=
            C.threshold_two k l hk hl hlk hactive
          obtain ⟨v, hv⟩ :=
            exists_large_blueDegree_of_globalRedDensity_lt
              G (by simpa using hn) hlt
          let B := blueNeighborsIn G v Finset.univ
          have hBcard :
              exponentThreshold F ε k (l - 1) ≤ B.card := by
            have hstep := C.blue_step k l hk hl hlk hactive
            have hv' :
                (exponentThreshold F ε k (l - 1) : ℝ) <
                  B.card := hstep.trans_lt (by simpa [B] using hv)
            exact_mod_cast hv'.le
          have hl2 : 2 ≤ l :=
            C.active_two k l hk hl hlk hactive
          have hprev :
              RamseyProperty k (l - 1)
                (exponentThreshold F ε k (l - 1)) :=
            ih (l - 1) (by omega) hk (by omega) (by omega)
          have hpropB : RamseyProperty k (l - 1) B.card :=
            Erdos1014.ramseyProperty_mono_vertices hBcard hprev
          rcases red_or_blue_of_ramseyProperty B hpropB with
            ⟨K, hKB, hK⟩ | ⟨K, hKB, hK⟩
          · exact hbad.1 K hK
          · have hKcompl : Gᶜ.IsNClique (l - 1) K := by
              simpa using hK
            have hinsCompl : Gᶜ.IsNClique l (insert v K) := by
              simpa [Nat.sub_add_cancel (by omega : 1 ≤ l)] using
                hKcompl.insert (fun u hu ↦ by
                  have huB : u ∈ B := hKB hu
                  exact (mem_redNeighborsIn Gᶜ v u Finset.univ).1
                    (by simpa [B, blueNeighborsIn] using huB) |>.2)
            have hins : G.IsNIndepSet l (insert v K) := by
              simpa using hinsCompl
            exact hbad.2 (insert v K) hins
      · exact C.base k l hk hl hlk hactive

/-- A family of certificates for every error tolerance proves the
uniform `o(k)` exponent statement. -/
theorem hasRamseyExponent_of_certificates
    {F : ℝ → ℝ}
    (hcert :
      ∀ ε : ℝ, 0 < ε →
        Nonempty (DescentCertificate F ε)) :
    HasRamseyExponent F := by
  intro ε hε
  obtain ⟨C⟩ := hcert ε hε
  refine ⟨C.cutoff, ?_⟩
  intro k l hk hl hlk
  have hprop :=
    ramseyProperty_exponentThreshold_of_certificate C k l hk hl hlk
  have hR :
      ramseyNumber k l ≤ exponentThreshold F ε k l :=
    Erdos1014.ramseyNumber_le_of_property hprop
  have hR' :
      (ramseyNumber k l : ℝ) ≤ exponentThreshold F ε k l := by
    exact_mod_cast hR
  exact hR'.trans (exponentThreshold_le_exp F ε k l)

end Arxiv2407_19026
