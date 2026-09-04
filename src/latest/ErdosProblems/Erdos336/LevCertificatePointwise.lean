import ErdosProblems.Erdos336.LevHighPowerReduction

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {N : ℕ} [NeZero N]

/-- Pointwise form of F-075: a single Lev-shaped certificate gives the
rank-or-dense certificate at that same cyclic high power. -/
theorem rankDenseCertificate_of_levCertificate
    (C : Set (ZMod N)) (t : ℕ) (ht : 15 ≤ t) (hzero : 0 ∈ C)
    (hprimitive : ∃ q : ℕ, ExactPower C q = Set.univ)
    (hdoub : 4 * (ExactPower C (2 * t)).ncard <
      9 * (ExactPower C t).ncard)
    (hlevcert : LevHighPowerCertificate C t) :
    RankDenseCertificate C t := by
  have htpos : 0 < t := by omega
  let S : Set (ZMod N) := ExactPower C t
  have hpower2 : ExactPower S 2 = ExactPower C (2 * t) := by
    simpa [S] using exactPower_exactPower C t 2
  rcases hlevcert with hdense | hrank | hexception
  · exact Or.inl hdense
  · obtain ⟨m, hm, π, hπ, α, L, V, hLpos, houter, hfiber, hdiff⟩ := hrank
    let : NeZero m := ⟨Nat.ne_of_gt hm⟩
    rw [hpower2] at hdiff
    have hLV : 4 * L * V < 5 * S.ncard := by
      change 4 * L * V < 5 * (ExactPower C t).ncard
      nlinarith
    by_cases hL : 15 ≤ L
    · by_cases hpair : ∃ p ∈ C, ∃ q ∈ C, π p ≠ π q
      · obtain ⟨α₀, L₀, p, q, hL₀, hL₀L, houterC, hp, hq, hpq⟩ :=
          exists_endpoint_subinterval π
            (fun x hx => houter x (subset_exactPower_of_zero_pos hzero htpos hx))
            hpair
        exact Or.inr ⟨m, hm, π, hπ, α, L, V, hL, houter, hfiber,
          hLV, α₀, L₀, p, q, hL₀, hL₀L, houterC, hp, hq, hpq⟩
      · have hm1 : m ≤ 1 := by
          simpa using card_target_le_one_of_no_image_pair π hπ hzero hprimitive hpair
        have hcard : Fintype.card (ZMod N) ≤ m * V :=
          card_le_modulus_mul_of_fiber_bound hm π hfiber
        have hmV : m * V ≤ V := by nlinarith [Nat.zero_le V]
        have hVLV : V ≤ L * V := by nlinarith [Nat.zero_le V]
        exact Or.inl (by omega)
    · have hLsmall : L + 1 ≤ t := by omega
      have himage : (π '' S).ncard ≤ L + 1 :=
        ncard_image_le_of_interval_support π houter
      have hsmall : (ExactPower (π '' C) t).ncard ≤ L + 1 := by
        rw [← image_exactPower]
        exact himage
      have hzero' : 0 ∈ π '' C := ⟨0, hzero, π.map_zero⟩
      have hprimitive' := exactPower_univ_image_of_surjective π hπ hprimitive
      have hmL : m ≤ L + 1 := by
        simpa using card_le_of_highPower_ncard_le
          hzero' hprimitive' hLsmall hsmall
      have hcard : Fintype.card (ZMod N) ≤ m * V :=
        card_le_modulus_mul_of_fiber_bound hm π hfiber
      have hmV : m * V ≤ (L + 1) * V := Nat.mul_le_mul_right V hmL
      have htwo : (L + 1) * V ≤ 2 * (L * V) := by
        have : L + 1 ≤ 2 * L := by omega
        nlinarith [Nat.zero_le V]
      exact Or.inl (by omega)
  · obtain ⟨m, hm, π, hπ, V, hfiber, himage, hdiff⟩ := hexception
    rw [hpower2] at hdiff
    have hdense := highPower_three_coset_exception_is_dense hm (by omega)
      π hπ hzero hprimitive hfiber himage hdiff hdoub
    exact Or.inl (by omega)


end Erdos336
