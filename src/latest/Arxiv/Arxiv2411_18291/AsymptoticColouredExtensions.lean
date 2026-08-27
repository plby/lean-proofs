import Arxiv.Arxiv2411_18291.ExtensionColourCriterion
import Arxiv.Arxiv2411_18291.ColourProbabilityNumerics
import Arxiv.Arxiv2411_18291.ColourCollisionNumerics

/-!
# Coloured extensions at polynomial scales

The moment criterion holds uniformly over root maps and prescribed extension
families of polynomial density. A polynomial marginal lower bound and a
smaller joint-probability error give a polynomial failure bound, together
with an actual successful colour assignment for each root problem.
-/

open Finset Filter MeasureTheory
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {I W : Type*} [Fintype W] [DecidableEq W] {q : ℕ}

theorem eventually_coloured_extensions (F : Finset W) (s : Finset I) (Q : I → Block W q)
    (r : ℕ) (hroot : ∀ i ∈ s, ((Q i).val ∩ F).card < r)
    {b c a β γ κ : ℝ} (hb : 0 < b) (hc : 0 < c) (hκ : 0 < κ) (hκγ : κ < γ)
    (hgap : a + 2 * β * s.card + κ < 1) :
    ∀ᶠ n : ℕ in atTop,
      ∀ [MeasurableSpace (Equiv.Perm (Fin n))] [MeasurableSingletonClass (Equiv.Perm (Fin n))],
      ∀ φ : F ↪ Fin n, ∀ T : Finset (EmbeddingExtension φ), ∀ D : Finset (Block (Fin n) q),
      ∀ d : ℝ, 0 ≤ d →
      (c * (n : ℝ) ^ (-a)) * (n : ℝ) ^ (Fintype.card W - F.card) ≤ T.card →
      b * (n : ℝ) ^ (-β) ≤ density D →
      (1 - (n : ℝ) ^ (-γ)) * d ≤ density D →
      (∀ j < r, ∀ P : IntersectingBlockPair (Fin n) q q j,
        (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure.real
          {σ | P.val.1 ∈ mapGraph σ.toEmbedding D ∧ P.val.2 ∈ mapGraph σ.toEmbedding D} ≤
          (1 + (n : ℝ) ^ (-γ)) * d ^ 2) →
      (RandomPermutation.probability I (Fin n)).real
        {ω | extensionColourCount φ s Q T D ω ≤ (T.card : ℝ) * density D ^ s.card / 2} ≤
        8 * (n : ℝ) ^ (-κ) ∧
      ∃ ω, (T.card : ℝ) * density D ^ s.card / 2 < extensionColourCount φ s Q T D ω := by
  have hsmall := (((tendsto_rpow_neg_atTop hκ).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 8).eventually
      (gt_mem_nhds (by norm_num : (8 : ℝ) * 0 < 1))
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_colour_joint_power_bound s.card (hκ.trans hκγ) hκγ,
    eventually_colour_collision_bound (Fintype.card W - F.card) s.card hb hc hgap,
    hsmall] with n hn hpowern hcollisionn hsn
  intro _ _ φ T D d hd hTsize hpbase hpd hpair
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hTpos : (0 : ℝ) < T.card :=
    (mul_pos (mul_pos hc (Real.rpow_pos_of_pos hnpos _)) (pow_pos hnpos _)).trans_le hTsize
  have hT : T.Nonempty := card_pos.mp (by exact_mod_cast hTpos)
  have hp : 0 < density D := (mul_pos hb (Real.rpow_pos_of_pos hnpos _)).trans_le hpbase
  let t := (1 + (n : ℝ) ^ (-γ)) * d ^ 2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpower : t ^ s.card ≤ (1 + (n : ℝ) ^ (-κ)) * density D ^ (2 * s.card) :=
    hpowern (density D) d t hd ht hpd le_rfl s.card le_rfl
  have hcollision : ((Fintype.card W - F.card : ℕ) : ℝ) ^ 2 *
      (Fintype.card (Fin n) : ℝ) ^ (Fintype.card W - F.card - 1) ≤
        (n : ℝ) ^ (-κ) * T.card * density D ^ (2 * s.card) := by
    simpa only [Fintype.card_fin] using hcollisionn (T.card : ℝ) (density D) hTsize hpbase
  have hbnd := extensionColourCount_lower_tail_le s Q T D r hT hp ht hroot hpair hpower hcollision
  refine ⟨hbnd, ?_⟩
  have hμ : (0 : ℝ) < T.card * density D ^ s.card := mul_pos hTpos (pow_pos hp _)
  have hm := extensionColourCount_relative_second_moment s Q T D r ht hroot hpair hpower hcollision
  dsimp only [Function.comp_def] at hsn
  exact RandomPermutation.eventCount_exists_many s T (fun f i => extensionColourEvent (Q i) f D)
    hμ (extensionColourCount_mean s Q T D) hm (by nlinarith only [hsn])

end Arxiv2411_18291
