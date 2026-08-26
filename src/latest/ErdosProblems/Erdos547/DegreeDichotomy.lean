import ErdosProblems.Erdos547.DegreeCleaning
import Mathlib.Data.Nat.Choose.Cast

/-!
# The degree dichotomy underlying the candidate proof

The majority colour has either a core of minimum degree close to the tree order,
or an induced graph satisfying the positive-proportion degree hypotheses. This
is a graph-theoretic reduction only: neither tree-embedding conclusion is assumed
or asserted here.
-/

namespace Erdos547

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The majority-colour edge count produces one of the two precise host
configurations used by the tree-embedding arguments. -/
theorem majority_core_dichotomy (S₀ : Finset V) (m : ℕ) (a ε : ℝ)
    (hcard : S₀.card = 2 * m) (ha : 0 < a) (hε : 0 < ε) (hε_small : ε ≤ 1)
    (ha_small : a ≤ ε ^ 2 / 1000) (hm : (100 : ℝ) ≤ m) (ham : 2 ≤ a * m)
    (hmass : 2 * (m : ℝ) ^ 2 - m ≤ degreeMass G S₀) :
    (∃ Q ⊆ S₀, Q.Nonempty ∧
      ∀ v ∈ Q, (1 - ε) * m ≤ (degreeIn G Q v : ℝ)) ∨
    (∃ S ⊆ S₀, (m : ℝ) / 2 ≤ S.card ∧
      (∀ v ∈ S, (1 + a) * m / 2 < (degreeIn G S v : ℝ)) ∧
      a * S.card ≤ (S.filter fun v ↦ (1 + a) * m ≤ (degreeIn G S v : ℝ)).card) := by
  classical
  have hm_pos : (0 : ℝ) < m := by linarith
  have hε_square : ε ^ 2 ≤ 1 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hε_small) (show 0 ≤ 1 + ε by linarith)
    nlinarith only [hprod]
  have ha_bound : a ≤ 1 / 100 := by nlinarith
  have ha_one : a ≤ 1 := by linarith
  obtain ⟨S, hSS₀, hSsize, hmin, hmassS⟩ :=
    exists_majority_degree_core G S₀ m a hcard ha ha_bound hm ham hmass
  let X := S.filter fun v ↦ (1 + a) * m ≤ (degreeIn G S v : ℝ)
  by_cases hlarge : a * S.card ≤ (X.card : ℝ)
  · exact Or.inr ⟨S, hSS₀, hSsize, hmin, hlarge⟩
  have hsmall : (X.card : ℝ) < a * S.card := lt_of_not_ge hlarge
  have hXS : X ⊆ S := Finset.filter_subset _ _
  have hSpos : (0 : ℝ) < S.card := by linarith
  have hXlt : X.card < S.card := by
    have hprod := mul_le_mul_of_nonneg_right ha_one hSpos.le
    have hreal : (X.card : ℝ) < S.card := by nlinarith
    exact_mod_cast hreal
  let J := S \ X
  have hJS : J ⊆ S := Finset.sdiff_subset
  have hJpos : J.Nonempty := by
    apply Finset.card_pos.mp
    dsimp [J]
    rw [Finset.card_sdiff_of_subset hXS]
    omega
  have hSupper : (S.card : ℝ) ≤ 2 * m := by
    have h := Finset.card_le_card hSS₀
    rw [hcard] at h
    exact_mod_cast h
  have hJupper : (J.card : ℝ) ≤ 2 * m := by
    have hle : (J.card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_le_card hJS
    exact hle.trans hSupper
  have hremoved : S \ J = X := Finset.sdiff_sdiff_eq_self hXS
  have hdrop := degreeMass_le_delete_add G hJS
  rw [hremoved] at hdrop
  have hmassJ : (1 - 8 * a) * m * J.card ≤ degreeMass G J := by
    have hprod₁ := mul_le_mul_of_nonneg_left hSupper
      (show 0 ≤ 2 * (X.card : ℝ) by positivity)
    have hprod₂ := mul_le_mul_of_nonneg_left hsmall.le
      (show (0 : ℝ) ≤ 4 * m by positivity)
    have hJle : (J.card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_le_card hJS
    have hcoef : 0 ≤ (1 - 8 * a) * m := by
      apply mul_nonneg
      · linarith
      · exact hm_pos.le
    have hprod₃ := mul_le_mul_of_nonneg_left hJle hcoef
    nlinarith only [hmassS, hdrop, hprod₁, hprod₂, hprod₃]
  have hmaxJ : ∀ v ∈ J, (degreeIn G J v : ℝ) ≤ (1 + a) * m := by
    intro v hv
    obtain ⟨hvs, hvx⟩ := Finset.mem_sdiff.mp hv
    have hnot : ¬ (1 + a) * m ≤ (degreeIn G S v : ℝ) := by
      intro h
      exact hvx (Finset.mem_filter.mpr ⟨hvs, h⟩)
    calc
      (degreeIn G J v : ℝ) ≤ degreeIn G S v := by
        exact_mod_cast degreeIn_mono G hJS v
      _ ≤ (1 + a) * m := (lt_of_not_ge hnot).le
  obtain ⟨Q, hQJ, hQpos, hQdeg⟩ := exists_near_regular_core G J m a ε hJpos hm_pos
    hJupper ha.le hε hε_small ha_small hmassJ hmaxJ
  exact Or.inl ⟨Q, hQJ.trans (hJS.trans hSS₀), hQpos, hQdeg⟩

/-- The majority colour supplies exactly the initial degree mass used above. -/
theorem majority_degreeMass {m : ℕ} (R : SimpleGraph (Fin (2 * m)))
    [DecidableRel R.Adj] [DecidableRel Rᶜ.Adj] :
    2 * (m : ℝ) ^ 2 - m ≤ degreeMass R Finset.univ ∨
      2 * (m : ℝ) ^ 2 - m ≤ degreeMass Rᶜ Finset.univ := by
  have hchoose : ((2 * m).choose 2 : ℝ) = 2 * (m : ℝ) ^ 2 - m := by
    rw [Nat.cast_choose_two]
    push_cast
    ring
  rcases majority_edge_count R with hr | hb
  · left
    rw [degreeMass_univ, ← hchoose]
    simp only [Fintype.card_fin] at hr
    exact_mod_cast hr
  · right
    rw [degreeMass_univ, ← hchoose]
    simp only [Fintype.card_fin] at hb
    exact_mod_cast hb

open scoped Classical in
/-- The degree dichotomy with its full uniform sufficiently-large quantifiers.
The constants depend only on `ε`, not on the colouring or on a guest tree. -/
theorem eventually_colour_degree_dichotomy (ε : ℝ) (hε : 0 < ε) (hε_small : ε ≤ 1) :
    ∃ a : ℝ, 0 < a ∧ a ≤ ε ^ 2 / 1000 ∧
      ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ R : SimpleGraph (Fin (2 * m)),
        ∃ G : SimpleGraph (Fin (2 * m)), (G = R ∨ G = Rᶜ) ∧
          ((∃ Q : Finset (Fin (2 * m)), Q.Nonempty ∧
            ∀ v ∈ Q, (1 - ε) * m ≤ (degreeIn G Q v : ℝ)) ∨
          (∃ S : Finset (Fin (2 * m)), (m : ℝ) / 2 ≤ S.card ∧
            (∀ v ∈ S, (1 + a) * m / 2 < (degreeIn G S v : ℝ)) ∧
            a * S.card ≤
              (S.filter fun v ↦ (1 + a) * m ≤ (degreeIn G S v : ℝ)).card)) := by
  classical
  let a : ℝ := ε ^ 2 / 1000
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt (max (100 : ℝ) (2 / a))
  refine ⟨a, ha, le_rfl, m₀, ?_⟩
  intro m hm R
  have hmn : (m₀ : ℝ) ≤ m := by exact_mod_cast hm
  have hm100 : (100 : ℝ) ≤ m :=
    (le_max_left _ _).trans (hm₀.le.trans hmn)
  have hratio : 2 / a ≤ (m : ℝ) :=
    (le_max_right _ _).trans (hm₀.le.trans hmn)
  have ham : 2 ≤ a * m := by
    have h := (div_le_iff₀ ha).mp hratio
    nlinarith only [h]
  have hconfig (G : SimpleGraph (Fin (2 * m)))
      (hG : 2 * (m : ℝ) ^ 2 - m ≤ degreeMass G Finset.univ) :
      (∃ Q : Finset (Fin (2 * m)), Q.Nonempty ∧
        ∀ v ∈ Q, (1 - ε) * m ≤ (degreeIn G Q v : ℝ)) ∨
      (∃ S : Finset (Fin (2 * m)), (m : ℝ) / 2 ≤ S.card ∧
        (∀ v ∈ S, (1 + a) * m / 2 < (degreeIn G S v : ℝ)) ∧
        a * S.card ≤
          (S.filter fun v ↦ (1 + a) * m ≤ (degreeIn G S v : ℝ)).card) := by
    rcases majority_core_dichotomy G Finset.univ m a ε (by simp) ha hε hε_small
        le_rfl hm100 ham hG with hnear | hpositive
    · obtain ⟨Q, _, hQ, hdeg⟩ := hnear
      exact Or.inl ⟨Q, hQ, hdeg⟩
    · obtain ⟨S, _, hsize, hdeg, hcount⟩ := hpositive
      exact Or.inr ⟨S, hsize, hdeg, hcount⟩
  rcases @majority_degreeMass m R (fun _ _ ↦ Classical.propDecidable _)
    (fun _ _ ↦ Classical.propDecidable _) with hr | hb
  · exact ⟨R, Or.inl rfl, hconfig R hr⟩
  · exact ⟨Rᶜ, Or.inr rfl, hconfig Rᶜ hb⟩

end Erdos547

#print axioms Erdos547.majority_core_dichotomy
#print axioms Erdos547.majority_degreeMass
#print axioms Erdos547.eventually_colour_degree_dichotomy
