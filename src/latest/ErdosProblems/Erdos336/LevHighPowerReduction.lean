import Mathlib
import ErdosProblems.Erdos336.ConditionalFiniteStructure
import ErdosProblems.Erdos336.HighPowerExceptionalDense
import ErdosProblems.Erdos336.ProgressionEndpointExtraction

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The three alternatives in Lev's strict `9/4` theorem, stated in the
homomorphic form needed for a primitive high power. -/
def LevHighPowerCertificate (C : Set G) (t : ℕ) : Prop :=
  let S := ExactPower C t
  Fintype.card G < 30000 * S.ncard ∨
  (∃ (m : ℕ) (_hm : 0 < m) (π : G →+ ZMod m), Function.Surjective π ∧
    ∃ (α : ZMod m) (L V : ℕ),
      0 < L ∧
      (∀ x ∈ S, ∃ k : ℕ, k ≤ L ∧ π x = α + (k : ZMod m)) ∧
      (∀ z : ZMod m, (homFiberFinset π z).card ≤ V) ∧
      S.ncard + L * V ≤ (ExactPower S 2).ncard) ∨
  (∃ (m : ℕ) (_hm : 0 < m) (π : G →+ ZMod m), Function.Surjective π ∧
    ∃ V : ℕ,
      (∀ z : ZMod m, (homFiberFinset π z).card ≤ V) ∧
      (π '' S).ncard ≤ 3 ∧
      S.ncard + 3 * V ≤ (ExactPower S 2).ncard)

/-- A faithful specialized interface for Lev's cyclic small-doubling theorem. -/
def HasLevHighPowerStructure : Prop :=
  ∀ (N : ℕ) (hN : 0 < N),
    let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
    ∀ (C : Set (ZMod N)) (t : ℕ),
      15 ≤ t → 0 ∈ C →
      (∃ q : ℕ, ExactPower C q = Set.univ) →
      4 * (ExactPower C (2 * t)).ncard <
        9 * (ExactPower C t).ncard →
      LevHighPowerCertificate C t

/-- A positive exact power contains its zero-containing root. -/
theorem subset_exactPower_of_zero_pos {C : Set G} (hzero : 0 ∈ C)
    {t : ℕ} (ht : 0 < t) : C ⊆ ExactPower C t := by
  intro x hx
  have hx1 : x ∈ ExactPower C 1 := by
    exact ⟨[x], by simp, by simpa, by simp⟩
  exact exactPower_mono_of_zero hzero (by omega) hx1

/-- A set supported on `L+1` labelled quotient fibres has image cardinal at
most `L+1`, even when the labels wrap around. -/
theorem ncard_image_le_of_interval_support
    {m L : ℕ} (π : G → ZMod m) {S : Set G} {α : ZMod m}
    (houter : ∀ x ∈ S, ∃ k : ℕ, k ≤ L ∧
      π x = α + (k : ZMod m)) :
    (π '' S).ncard ≤ L + 1 := by
  classical
  let P : Finset (ZMod m) := Finset.image
    (fun k : ℕ => α + (k : ZMod m)) (Finset.range (L + 1))
  have hsub : π '' S ⊆ (P : Set (ZMod m)) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, hk, hπ⟩ := houter x hx
    rw [hπ]
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr
      ⟨k, Finset.mem_range.mpr (by omega), rfl⟩)
  calc
    (π '' S).ncard ≤ (P : Set (ZMod m)).ncard := Set.ncard_le_ncard hsub
    _ = P.card := Set.ncard_coe_finset P
    _ ≤ (Finset.range (L + 1)).card := by
      dsimp [P]
      exact Finset.card_image_le
    _ = L + 1 := Finset.card_range _

/-- If a primitive set has no two distinct values under a surjective finite
quotient map, then that quotient has at most one point. -/
theorem card_target_le_one_of_no_image_pair
    {Q : Type*} [AddCommGroup Q] [Fintype Q]
    (f : G →+ Q) (hf : Function.Surjective f)
    {C : Set G} (hzero : 0 ∈ C)
    (hprimitive : ∃ q : ℕ, ExactPower C q = Set.univ)
    (hpair : ¬ ∃ p ∈ C, ∃ q ∈ C, f p ≠ f q) :
    Fintype.card Q ≤ 1 := by
  have hDsub : f '' C ⊆ ({0} : Set Q) := by
    rintro _ ⟨x, hx, rfl⟩
    have hfx : f x = f 0 := by
      by_contra hne
      exact hpair ⟨x, hx, 0, hzero, hne⟩
    simpa using hfx
  obtain ⟨r, hr⟩ := exactPower_univ_image_of_surjective f hf hprimitive
  have hpowsub : ExactPower (f '' C) r ⊆ ExactPower ({0} : Set Q) r := by
    rintro y ⟨xs, hlen, hmem, hsum⟩
    refine ⟨xs, hlen, ?_, hsum⟩
    intro z hz
    exact hDsub (hmem z hz)
  have hzeroPowerAll : ∀ n : ℕ, ExactPower ({0} : Set Q) n = {0} := by
    intro n
    rw [exactPower_eq_nsmul]
    induction n with
    | zero =>
        rw [zero_nsmul]
        rfl
    | succ n ih => rw [succ_nsmul, ih]; simp
  have hzeroPower := hzeroPowerAll r
  have huniv : (Set.univ : Set Q) ⊆ {0} := by
    rw [← hr, ← hzeroPower]
    exact hpowsub
  rw [Fintype.card_le_one_iff]
  intro x y
  have hx := huniv (Set.mem_univ x)
  have hy := huniv (Set.mem_univ y)
  simpa only [Set.mem_singleton_iff] using hx.trans hy.symm

/-- The specialized Lev alternatives imply exactly the rank-or-dense
certificate isolated in F-067. -/
theorem highPowerRankDenseStructure_of_lev
    (hlev : HasLevHighPowerStructure) :
    HasHighPowerRankDenseStructure := by
  intro N hN
  dsimp only
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  intro C t ht hzero hprimitive hdoub
  have htpos : 0 < t := by omega
  let S : Set (ZMod N) := ExactPower C t
  have hlevcert : LevHighPowerCertificate C t :=
    hlev N hN C t ht hzero hprimitive hdoub
  have hpower2 : ExactPower S 2 = ExactPower C (2 * t) := by
    simpa [S] using exactPower_exactPower C t 2
  rcases hlevcert with hdense | hrank | hexception
  · exact Or.inl hdense
  · obtain ⟨m, hm, π, hπ, α, L, V, hLpos, houter, hfiber, hdiff⟩ := hrank
    letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
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
