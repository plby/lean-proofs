import ErdosProblems.Erdos336.RectifiableThreeMinusThreeReduction
import ErdosProblems.Erdos336.CyclicQuotientCardinality

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {N : ℕ} [NeZero N]

/-- A rank-one finset certificate lifts through a cyclic subgroup quotient,
with the fibre bound multiplied by the kernel cardinality, provided the
quotient doubling defect scales into the parent defect. -/
theorem finsetRankCertificate_of_cyclicQuotient
    (K : AddSubgroup (ZMod N)) [NeZero (Nat.card (ZMod N ⧸ K))]
    (A : Finset (ZMod N)) (hAne : A.Nonempty)
    (hchild : FinsetRankCertificate (A.image (cyclicQuotientHom K)))
    (hdefect :
      ((A.image (cyclicQuotientHom K) +
          A.image (cyclicQuotientHom K)).card -
        (A.image (cyclicQuotientHom K)).card) *
          (addSubgroupFinset K).card ≤
        (A + A).card - A.card) :
    FinsetRankCertificate A := by
  let f := cyclicQuotientHom K
  let k := (addSubgroupFinset K).card
  have hf : Function.Surjective f := cyclicQuotientHom_surjective K
  rcases hchild with
    ⟨n, hn, π, hπ, α, L, V, hL, houter, hfiber, hcost⟩
  change (A.image f).card + L * V ≤
    (A.image f + A.image f).card at hcost
  change (((A.image f + A.image f).card - (A.image f).card) * k ≤
    (A + A).card - A.card) at hdefect
  let π' : ZMod N →+ ZMod n := π.comp f
  refine ⟨n, hn, π', hπ.comp hf, α, L, V * k, hL, ?_, ?_, ?_⟩
  · intro x hx
    have hfx : f x ∈ A.image f := Finset.mem_image.mpr ⟨x, hx, rfl⟩
    exact houter (f x) hfx
  · intro z
    have heq : homFiberFinset π' z =
        homPreimageFinset f (homFiberFinset π z) := by
      ext x
      simp [π', homPreimageFinset]
    rw [heq, card_homPreimageFinset f hf]
    have hker : f.ker = K := by simp [f]
    rw [hker]
    simpa [k] using Nat.mul_le_mul_right k (hfiber z)
  · have hLV : L * V ≤
        (A.image f + A.image f).card - (A.image f).card := by
      omega
    have hscaledRaw := Nat.mul_le_mul_right k hLV
    have hscaled : L * (V * k) ≤
        ((A.image f + A.image f).card - (A.image f).card) * k := by
      simpa [mul_assoc] using hscaledRaw
    have hparent : L * (V * k) ≤ (A + A).card - A.card := by
      exact le_trans hscaled hdefect
    have hAle : A.card ≤ (A + A).card :=
      Finset.card_le_card_add_left hAne
    omega

end Erdos336
