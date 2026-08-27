import Arxiv.Arxiv2411_18291.BoundedMultiplicityCorrection

/-!
# Uniform bounded representations at any fixed edge multiplicity

An integral generating family with multiplicity at most `M` can be augmented
by sparse local decoders so that every generated leave has a representation
with coefficients bounded by `(M+1)*2^q*r!`. In particular, absorption can
use a fixed multiplicity constant other than two.
-/

open Finset Filter

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r M : ℕ}

theorem bounded_multiplicity_representation_of_local_decoders (hqr : r + 1 < q)
    (D : Finset (Block V q)) (B L : Hypergraph V (r + 1))
    (hDB : cliqueSupport (r + 1) D ⊆ B) (hLB : L ⊆ B)
    (hmult : ∀ e : Block V (r + 1), (D.filter fun Q => e.val ⊆ Q.val).card ≤ M)
    (Z : B → Block V (q + (r + 1)))
    (hZ : IsCliqueCover (complete V (r + 1) \ B) (fun e : B => e.val) Z)
    (hgen : GeneratedBy D (indicator L)) :
    ∃ Φ : Block V q → ℤ, boundary (r + 1) Φ = indicator L ∧
      (∀ Q, Q ∉ D ∪ cliqueRefinement q (univ.image Z) → Φ Q = 0) ∧
      ∀ Q, |Φ Q| ≤ ((M + 1) * (2 ^ q * (r + 1).factorial) : ℕ) := by
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
  have hc (i : B) : |c i| ≤ (M : ℤ) :=
    reduced_boundary_correction_abs_le N hN D L Φ₀ hΦ₀ hs₀ hmult i.val
  have hprod (i : B) : N * c i = J i.val := Int.mul_ediv_cancel_of_dvd (hdiv i.val)
  have hsJ : ∀ e, e ∉ B → J e = 0 := by
    intro e he
    have heL : e ∉ L := fun heL => he (hLB heL)
    dsimp only [J]
    rw [indicator_apply_of_notMem heL, boundary_zero_outside_support D B Φ₁ hs₁ hDB e he]
    exact sub_self _
  have hΦ₂ := boundary_sumLocalDecoders hqr.le Z (fun i => (hZ.punctured i).1) c J hsJ hprod
  refine ⟨Φ₁ + sumLocalDecoders Z c, ?_, ?_, ?_⟩
  · rw [boundary_add, hΦ₂]
    funext e
    simp only [Pi.add_apply, J, add_sub_cancel]
  · intro Q hQ
    have hQ₁ : Q ∉ D := fun h => hQ (mem_union_left _ h)
    have hQ₂ : Q ∉ cliqueRefinement q (univ.image Z) := fun h => hQ (mem_union_right _ h)
    simp only [Pi.add_apply, hs₁ Q hQ₁, sumLocalDecoders_support Z c Q hQ₂, add_zero]
  · intro Q
    have hΦ₁ : |Φ₁ Q| ≤ (2 ^ q * (r + 1).factorial : ℕ) := by
      rw [abs_of_nonneg (Int.emod_nonneg _ hNpos.ne')]
      exact (Int.emod_lt_of_pos (Φ₀ Q) hNpos).le.trans hNC
    have hcQ := hZ.sumLocalDecoders_abs_le_mul hqr.le c (Nat.cast_nonneg M) hc Q
    rw [Pi.add_apply]
    calc
      _ ≤ |Φ₁ Q| + |sumLocalDecoders Z c Q| := abs_add_le _ _
      _ ≤ (2 ^ q * (r + 1).factorial : ℕ) +
          (M : ℤ) * (2 ^ q * (r + 1).factorial : ℕ) := add_le_add hΦ₁ hcQ
      _ = _ := by push_cast; ring

omit [Fintype V] [DecidableEq V] in
theorem eventually_exists_bounded_multiplicity_representation_family
    (hqr : r + 1 < q) (M : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    let C : ℝ := 1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1)
    ∀ᶠ n : ℕ in atTop, ∀ B : Hypergraph (Fin n) (r + 1),
      ∀ D₁ : Finset (Block (Fin n) q), IsGraphBounded B ((n : ℝ) ^ (-ρ)) →
      cliqueSupport (r + 1) D₁ ⊆ B →
      (∀ e : Block (Fin n) (r + 1), (D₁.filter fun Q => e.val ⊆ Q.val).card ≤ M) →
      ∃ D₂ : Finset (Block (Fin n) q), IsLocalDecoderFamily B D₂ ∧
        IsGraphBounded (cliqueSupport (r + 1) D₂) (C * (n : ℝ) ^ (-ρ)) ∧
        ∀ L : Hypergraph (Fin n) (r + 1), L ⊆ B → GeneratedBy D₁ (indicator L) →
          ∃ Φ : Block (Fin n) q → ℤ, boundary (r + 1) Φ = indicator L ∧
            (∀ Q, Q ∉ D₁ ∪ D₂ → Φ Q = 0) ∧
            ∀ Q, |Φ Q| ≤ ((M + 1) * (2 ^ q * (r + 1).factorial) : ℕ) := by
  dsimp only
  filter_upwards [eventually_exists_sparse_local_decoders hqr.le hρ hρ1] with n hn
  intro B D₁ hB hDB hmult
  obtain ⟨Z, D₂, hZ, rfl, hD₂, hb⟩ := hn B hB
  exact ⟨_, hD₂, hb, fun L hLB hgen =>
    bounded_multiplicity_representation_of_local_decoders hqr D₁ B L hDB hLB hmult Z hZ hgen⟩

end Arxiv2411_18291
