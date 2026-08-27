import Arxiv.Arxiv2411_18291.DecoderCorrection

/-!
# Bounded integral representations before splitting

The first algebraic step in the proof of the absorber lemma is now exact:
an integral representation on a family of edge multiplicity at most two
can be replaced by one on that family and its separated local decoders,
with every coefficient bounded by `2^q*r!`. The sparse decoder family is
chosen uniformly for all represented leaves, not separately for each leave.
-/

open Finset Filter

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem bounded_representation_of_local_decoders (hqr : r + 1 < q)
    (D : Finset (Block V q)) (B L : Hypergraph V (r + 1))
    (hDB : cliqueSupport (r + 1) D ⊆ B) (hLB : L ⊆ B)
    (hmult : ∀ e : Block V (r + 1), (D.filter fun Q => e.val ⊆ Q.val).card ≤ 2)
    (Z : B → Block V (q + (r + 1)))
    (hZ : IsCliqueCover (complete V (r + 1) \ B) (fun e : B => e.val) Z)
    (hgen : GeneratedBy D (indicator L)) :
    ∃ Φ : Block V q → ℤ, boundary (r + 1) Φ = indicator L ∧
      (∀ Q, Q ∉ D ∪ cliqueRefinement q (univ.image Z) → Φ Q = 0) ∧
      ∀ Q, |Φ Q| ≤ (2 ^ q * (r + 1).factorial : ℕ) := by
  obtain ⟨Φ₀, hΦ₀, hs₀⟩ := hgen
  let N : ℤ := ((r + 1).factorial * q.choose (r + 1) : ℕ)
  have hN : 2 ≤ N := (decoder_multiplier_bounds hqr).1
  have hNC : N ≤ (2 ^ q * (r + 1).factorial : ℕ) := (decoder_multiplier_bounds hqr).2
  have hNpos : 0 < N := by omega
  let Φ₁ : Block V q → ℤ := fun Q => Φ₀ Q % N
  let J : Block V (r + 1) → ℤ := fun e => indicator L e - boundary (r + 1) Φ₁ e
  let c : B → ℤ := fun i => J i.val / N
  have hs₁ : ∀ Q, Q ∉ D → Φ₁ Q = 0 := by
    intro Q hQ
    dsimp only [Φ₁]
    rw [hs₀ Q hQ, Int.zero_emod]
  have hdiv (e : Block V (r + 1)) : N ∣ J e := by
    simpa only [hΦ₀, J, Φ₁] using boundary_remainder_congr N Φ₀ e
  have hc (i : B) : c i = -1 ∨ c i = 0 :=
    reduced_boundary_correction_small N hN D L Φ₀ hΦ₀ hs₀ hmult i.val
  have hprod (i : B) : N * c i = J i.val := Int.mul_ediv_cancel_of_dvd (hdiv i.val)
  have hsJ : ∀ e, e ∉ B → J e = 0 := by
    intro e he
    have heL : e ∉ L := fun heL => he (hLB heL)
    dsimp only [J]
    rw [indicator_apply_of_notMem heL, boundary_zero_outside_support D B Φ₁ hs₁ hDB e he]
    exact sub_self _
  have hΦ₂ := boundary_sumLocalDecoders hqr.le Z (fun i => (hZ.punctured i).1) c J hsJ hprod
  have hsep := hZ.refinement_disjoint_base hqr D hDB
  refine ⟨Φ₁ + sumLocalDecoders Z c, ?_, ?_, ?_⟩
  · rw [boundary_add, hΦ₂]
    funext e
    simp only [Pi.add_apply, J, add_sub_cancel]
  · intro Q hQ
    have hQ₁ : Q ∉ D := fun h => hQ (mem_union_left _ h)
    have hQ₂ : Q ∉ cliqueRefinement q (univ.image Z) := fun h => hQ (mem_union_right _ h)
    simp only [Pi.add_apply, hs₁ Q hQ₁, sumLocalDecoders_support Z c Q hQ₂, add_zero]
  · intro Q
    by_cases hQD : Q ∈ D
    · have hQ₂ : Q ∉ cliqueRefinement q (univ.image Z) :=
        fun h => disjoint_left.mp hsep hQD h
      rw [Pi.add_apply, sumLocalDecoders_support Z c Q hQ₂, add_zero,
        abs_of_nonneg (Int.emod_nonneg _ hNpos.ne')]
      exact (Int.emod_lt_of_pos (Φ₀ Q) hNpos).le.trans hNC
    · rw [Pi.add_apply, hs₁ Q hQD, zero_add]
      exact hZ.sumLocalDecoders_abs_le hqr.le c hc Q

omit [Fintype V] [DecidableEq V] in
theorem eventually_exists_bounded_representation_family (hqr : r + 1 < q) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    let C : ℝ := 1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1)
    ∀ᶠ n : ℕ in atTop, ∀ B : Hypergraph (Fin n) (r + 1),
      ∀ D₁ : Finset (Block (Fin n) q), IsGraphBounded B ((n : ℝ) ^ (-ρ)) →
      cliqueSupport (r + 1) D₁ ⊆ B →
      (∀ e : Block (Fin n) (r + 1), (D₁.filter fun Q => e.val ⊆ Q.val).card ≤ 2) →
      ∃ D₂ : Finset (Block (Fin n) q), IsLocalDecoderFamily B D₂ ∧
        IsGraphBounded (cliqueSupport (r + 1) D₂) (C * (n : ℝ) ^ (-ρ)) ∧
        ∀ L : Hypergraph (Fin n) (r + 1), L ⊆ B → GeneratedBy D₁ (indicator L) →
          ∃ Φ : Block (Fin n) q → ℤ, boundary (r + 1) Φ = indicator L ∧
            (∀ Q, Q ∉ D₁ ∪ D₂ → Φ Q = 0) ∧
            ∀ Q, |Φ Q| ≤ (2 ^ q * (r + 1).factorial : ℕ) := by
  dsimp only
  filter_upwards [eventually_exists_sparse_local_decoders hqr.le hρ hρ1] with n hn
  intro B D₁ hB hDB hmult
  obtain ⟨Z, D₂, hZ, rfl, hD₂, hb⟩ := hn B hB
  exact ⟨_, hD₂, hb, fun L hLB hgen =>
    bounded_representation_of_local_decoders hqr D₁ B L hDB hLB hmult Z hZ hgen⟩

end Arxiv2411_18291
