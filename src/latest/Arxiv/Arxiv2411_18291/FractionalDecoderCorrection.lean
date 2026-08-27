import Arxiv.Arxiv2411_18291.AveragedLocalDecoders

/-!
# Exact correction of real edge weights using averaged decoders

An edge error supported on a graph is corrected exactly by averaging local
decoders. If every decoding set is a clique of that graph, the correction
also uses only graph cliques. Bounds making the corrected coefficients
valid sampling probabilities are separate from this exact identity.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

def fractionalDecoderCorrection (G : Hypergraph V r)
    (Z : Block V r → Finset (Block V (q + r))) (c : Block V r → ℝ) : Block V q → ℝ :=
  ∑ e ∈ G, fun Q => c e * averagedLocalDecoder q (Z e) e Q

theorem boundary_fractionalDecoderCorrection (hqr : r ≤ q) (G : Hypergraph V r)
    (Z : Block V r → Finset (Block V (q + r))) (hZ : ∀ e ∈ G, (Z e).Nonempty)
    (hroot : ∀ e ∈ G, ∀ z ∈ Z e, e.val ⊆ z.val) (c : Block V r → ℝ) :
    boundary r (fractionalDecoderCorrection G Z c) = fun e => if e ∈ G then c e else 0 := by
  rw [fractionalDecoderCorrection, boundary_sum]
  funext f
  simp only [Finset.sum_apply]
  have hterm (e : Block V r) (he : e ∈ G) :
      boundary r (fun Q => c e * averagedLocalDecoder q (Z e) e Q) f =
        if e = f then c e else 0 := by
    rw [boundary_mul, boundary_averagedLocalDecoder hqr (Z e) (hZ e he) e (hroot e he)]
    by_cases h : e = f
    · subst e
      simp
    · simp only [if_neg h, if_neg (Ne.symm h), mul_zero]
  rw [sum_congr rfl hterm]
  simp

theorem fractionalDecoderCorrection_eq_zero (G : Hypergraph V r)
    (Z : Block V r → Finset (Block V (q + r)))
    (hZ : ∀ e ∈ G, ∀ z ∈ Z e, cliqueEdges r z ⊆ G)
    (c : Block V r → ℝ) (Q : Block V q) (hQ : ¬cliqueEdges r Q ⊆ G) :
    fractionalDecoderCorrection G Z c Q = 0 := by
  simp only [fractionalDecoderCorrection, Finset.sum_apply]
  apply sum_eq_zero
  intro e he
  rw [averagedLocalDecoder_eq_zero (Z e) e Q, mul_zero]
  intro z hz hQz
  apply hQ
  intro f hf
  exact hZ e he z hz ((mem_cliqueEdges _ _).mpr (((mem_cliqueEdges _ _).mp hf).trans hQz))

theorem boundary_add_fractionalDecoderCorrection (hqr : r ≤ q) (G : Hypergraph V r)
    (Z : Block V r → Finset (Block V (q + r))) (hZ : ∀ e ∈ G, (Z e).Nonempty)
    (hroot : ∀ e ∈ G, ∀ z ∈ Z e, e.val ⊆ z.val)
    (w : Block V q → ℝ) (J : Block V r → ℝ)
    (hs : ∀ e, e ∉ G → boundary r w e = J e) :
    boundary r (w + fractionalDecoderCorrection G Z (J - boundary r w)) = J := by
  rw [boundary_add, boundary_fractionalDecoderCorrection hqr G Z hZ hroot]
  funext e
  by_cases he : e ∈ G
  · simp only [Pi.add_apply, if_pos he, Pi.sub_apply]
    ring
  · simp only [Pi.add_apply, if_neg he, add_zero, hs e he]

end Arxiv2411_18291
