import Arxiv.Arxiv2411_18291.ExtensionColourMoments
import Arxiv.Arxiv2411_18291.PermutationCountSuccess
import Arxiv.Arxiv2411_18291.Neighborhood

/-!
# A finite lower-tail criterion for coloured extensions

The powered joint-probability error and the geometric collision term each
contribute one relative error to the second moment. The resulting lower-tail
probability is at most eight times that error.
-/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

theorem colour_second_moment_scale {A p t ε R : ℝ} (hA : 0 ≤ A) (M : ℕ)
    (hpower : t ^ M ≤ (1 + ε) * p ^ (2 * M))
    (hcollision : R ≤ ε * A * p ^ (2 * M)) :
    A ^ 2 * t ^ M + A * R ≤ (1 + 2 * ε) * (A * p ^ M) ^ 2 := by
  have ht := mul_le_mul_of_nonneg_left hpower (sq_nonneg A)
  have hc := mul_le_mul_of_nonneg_left hcollision hA
  have hp : p ^ (2 * M) = (p ^ M) ^ 2 := by rw [Nat.mul_comm 2 M, pow_mul]
  rw [hp] at ht hc
  nlinarith only [ht, hc]

variable {I W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {q : ℕ} {φ : F ↪ V}
variable [MeasurableSpace (Equiv.Perm V)] [MeasurableSingletonClass (Equiv.Perm V)]

theorem extensionColourCount_relative_second_moment (s : Finset I) (Q : I → Block W q)
    (T : Finset (EmbeddingExtension φ)) (D : Finset (Block V q)) (r : ℕ) {t ε : ℝ}
    (ht : 0 ≤ t) (hroot : ∀ i ∈ s, ((Q i).val ∩ F).card < r)
    (hpair : ∀ a < r, ∀ P : IntersectingBlockPair V q q a,
      (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real
        {σ | P.val.1 ∈ mapGraph σ.toEmbedding D ∧ P.val.2 ∈ mapGraph σ.toEmbedding D} ≤ t)
    (hpower : t ^ s.card ≤ (1 + ε) * density D ^ (2 * s.card))
    (hcollision : ((Fintype.card W - F.card : ℕ) : ℝ) ^ 2 *
      (Fintype.card V : ℝ) ^ (Fintype.card W - F.card - 1) ≤
        ε * T.card * density D ^ (2 * s.card)) :
    (∫ ω, extensionColourCount φ s Q T D ω ^ 2 ∂RandomPermutation.probability I V) ≤
      (1 + 2 * ε) * ((T.card : ℝ) * density D ^ s.card) ^ 2 := by
  have hm := extensionColourCount_second_moment_le s Q T D r ht hroot hpair
  have hb := colour_second_moment_scale (Nat.cast_nonneg T.card) s.card hpower hcollision
  exact hm.trans (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hb)

theorem extensionColourCount_lower_tail_le (s : Finset I) (Q : I → Block W q)
    (T : Finset (EmbeddingExtension φ)) (D : Finset (Block V q)) (r : ℕ) {t ε : ℝ}
    (hT : T.Nonempty) (hp : 0 < density D) (ht : 0 ≤ t)
    (hroot : ∀ i ∈ s, ((Q i).val ∩ F).card < r)
    (hpair : ∀ a < r, ∀ P : IntersectingBlockPair V q q a,
      (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real
        {σ | P.val.1 ∈ mapGraph σ.toEmbedding D ∧ P.val.2 ∈ mapGraph σ.toEmbedding D} ≤ t)
    (hpower : t ^ s.card ≤ (1 + ε) * density D ^ (2 * s.card))
    (hcollision : ((Fintype.card W - F.card : ℕ) : ℝ) ^ 2 *
      (Fintype.card V : ℝ) ^ (Fintype.card W - F.card - 1) ≤
        ε * T.card * density D ^ (2 * s.card)) :
    (RandomPermutation.probability I V).real
      {ω | extensionColourCount φ s Q T D ω ≤ (T.card : ℝ) * density D ^ s.card / 2} ≤ 8 * ε := by
  have hμ : (0 : ℝ) < T.card * density D ^ s.card :=
    mul_pos (by exact_mod_cast hT.card_pos) (pow_pos hp _)
  have hm := extensionColourCount_relative_second_moment s Q T D r ht hroot hpair hpower hcollision
  have hb := RandomPermutation.eventCount_lower_tail_le s T
    (fun f i => extensionColourEvent (Q i) f D) hμ (extensionColourCount_mean s Q T D) hm
  calc
    _ ≤ 4 * (2 * ε) := hb
    _ = _ := by ring

theorem extensionColourCount_lower_tail_three_quarters_le (s : Finset I) (Q : I → Block W q)
    (T : Finset (EmbeddingExtension φ)) (D : Finset (Block V q)) (r : ℕ) {t ε : ℝ}
    (hT : T.Nonempty) (hp : 0 < density D) (ht : 0 ≤ t)
    (hroot : ∀ i ∈ s, ((Q i).val ∩ F).card < r)
    (hpair : ∀ a < r, ∀ P : IntersectingBlockPair V q q a,
      (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real
        {σ | P.val.1 ∈ mapGraph σ.toEmbedding D ∧ P.val.2 ∈ mapGraph σ.toEmbedding D} ≤ t)
    (hpower : t ^ s.card ≤ (1 + ε) * density D ^ (2 * s.card))
    (hcollision : ((Fintype.card W - F.card : ℕ) : ℝ) ^ 2 *
      (Fintype.card V : ℝ) ^ (Fintype.card W - F.card - 1) ≤
        ε * T.card * density D ^ (2 * s.card)) :
    (RandomPermutation.probability I V).real
      {ω | extensionColourCount φ s Q T D ω ≤ 3 * ((T.card : ℝ) * density D ^ s.card) / 4} ≤
        32 * ε := by
  have hμ : (0 : ℝ) < T.card * density D ^ s.card :=
    mul_pos (by exact_mod_cast hT.card_pos) (pow_pos hp _)
  have hm := extensionColourCount_relative_second_moment s Q T D r ht hroot hpair hpower hcollision
  have hb := RandomPermutation.eventCount_lower_tail_three_quarters_le s T
    (fun f i => extensionColourEvent (Q i) f D) hμ (extensionColourCount_mean s Q T D) hm
  calc
    _ ≤ 16 * (2 * ε) := hb
    _ = _ := by ring

end Arxiv2411_18291
