import ErdosProblems.Erdos438.LOSOdd
import ErdosProblems.Erdos438.LOSTwoPower

/-!
# The Lagarias--Odlyzko--Shearer modular bound

This file assembles the odd uniform triangle cover and the sharp two-primary
estimate through the Chinese remainder theorem.  The intermediate relation is
looped: diagonal pairs are retained, exactly as required by the literal
sumset condition `B + B`.
-/

namespace Erdos438

open scoped BigOperators

private def colorFibers {u : ℕ} (A : Finset (ZMod u × Fin 3))
    (x : ZMod u) : Finset (Fin 3) :=
  Finset.univ.filter fun c ↦ (x, c) ∈ A

private lemma sum_colorFibers_card {u : ℕ} [NeZero u]
    (A : Finset (ZMod u × Fin 3)) :
    (∑ x : ZMod u, (colorFibers A x).card) = A.card := by
  classical
  have hfiber (x : ZMod u) :
      (colorFibers A x).card = (A.filter fun p ↦ p.1 = x).card := by
    apply Finset.card_bij (fun c _ ↦ (x, c))
    · intro c hc
      simp only [Finset.mem_filter]
      exact ⟨by simpa [colorFibers] using hc, trivial⟩
    · intro c₁ _ c₂ _ h
      exact congrArg Prod.snd h
    · rintro ⟨y, c⟩ hp
      simp only [Finset.mem_filter] at hp
      refine ⟨c, ?_, ?_⟩
      · simpa [colorFibers, hp.2] using hp.1
      · simp [hp.2]
  symm
  rw [Finset.card_eq_sum_card_fiberwise (s := A) (t := Finset.univ)
    (f := Prod.fst) (by simp)]
  apply Finset.sum_congr rfl
  intro x _
  exact (hfiber x).symm

private lemma colorFibers_squareSumColoring {u : ℕ} [NeZero u]
    (A : Finset (ZMod u × Fin 3))
    (hA : RelIndependent (RelProd (SquareSumRel u) K3Rel) A) :
    ∀ x y, IsSquare (x + y) →
      ∀ c ∈ colorFibers A x, ∀ d ∈ colorFibers A y, c = d := by
  intro x y hxy c hc d hd
  by_contra hcd
  apply hA (x := (x, c)) (y := (y, d))
  · simpa [colorFibers] using hc
  · simpa [colorFibers] using hd
  · refine ⟨?_, hcd⟩
    rcases hxy with ⟨z, hz⟩
    exact ⟨z, by simpa [pow_two] using hz.symm⟩

private lemma independent_card_le_of_coloring_bound {u : ℕ} [NeZero u]
    (htwo : ∀ F : ZMod u → Finset (Fin 3),
      (∀ x y, IsSquare (x + y) → ∀ c ∈ F x, ∀ d ∈ F y, c = d) →
      32 * ∑ x, (F x).card ≤ 33 * u)
    (A : Finset (ZMod u × Fin 3))
    (hA : RelIndependent (RelProd (SquareSumRel u) K3Rel) A) :
    A.card ≤ (33 * u) / 32 := by
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 32)).2
  rw [mul_comm, ← sum_colorFibers_card A]
  exact htwo (colorFibers A) (colorFibers_squareSumColoring A hA)

private def crtImage {u v : ℕ} (h : u.Coprime v)
    (B : Finset (ZMod (u * v))) : Finset (ZMod u × ZMod v) :=
  B.image (ZMod.chineseRemainder h)

private lemma card_crtImage {u v : ℕ} (h : u.Coprime v)
    (B : Finset (ZMod (u * v))) :
    (crtImage h B).card = B.card := by
  rw [crtImage, Finset.card_image_iff.mpr]
  exact (ZMod.chineseRemainder h).injective.injOn

private lemma crtImage_independent {u v : ℕ} (h : u.Coprime v)
    (B : Finset (ZMod (u * v)))
    (hB : ∀ a ∈ B, ∀ b ∈ B, ¬ IsSquare (a + b)) :
    RelIndependent (RelProd (SquareSumRel u) (SquareSumRel v)) (crtImage h B) := by
  intro p hp q hq hpq
  rw [crtImage, Finset.mem_image] at hp hq
  obtain ⟨a, ha, rfl⟩ := hp
  obtain ⟨b, hb, rfl⟩ := hq
  have hab : SquareSumRel (u * v) a b :=
    (squareSumRel_chineseRemainder h a b).2 hpq
  rcases hab with ⟨z, hz⟩
  exact hB a ha b hb ⟨z, by simpa [pow_two] using hz.symm⟩

private lemma cancel_cover_bound
    {D v u b k f : ℕ} (hD : 0 < D) (hpull : D * b ≤ f * k)
    (htwo : 32 * k ≤ 33 * u) (hcover : 3 * f = D * v) :
    32 * b ≤ 11 * (u * v) := by
  have hmul : D * (32 * b) ≤ D * (11 * (u * v)) := by
    calc
      D * (32 * b) = 32 * (D * b) := by ring
      _ ≤ 32 * (f * k) := Nat.mul_le_mul_left 32 hpull
      _ = f * (32 * k) := by ring
      _ ≤ f * (33 * u) := Nat.mul_le_mul_left f htwo
      _ = 11 * u * (3 * f) := by ring
      _ = D * (11 * (u * v)) := by rw [hcover]; ring
  exact Nat.le_of_mul_le_mul_left hmul hD

private theorem los_modular_of_uniform_odd_cover
    {u v : ℕ} [NeZero u] [NeZero v] (huv : u.Coprime v)
    (htwo : ∀ F : ZMod u → Finset (Fin 3),
      (∀ x y, IsSquare (x + y) → ∀ c ∈ F x, ∀ d ∈ F y, c = d) →
      32 * ∑ x, (F x).card ≤ 33 * u)
    {D : ℕ} {F : Multiset (Fin 3 → ZMod v)}
    (hD : 0 < D) (hUniform : UniformCover F D)
    (hCover : IsRelCover K3Rel (SquareSumRel v) F)
    (B : Finset (ZMod (u * v)))
    (hB : ∀ a ∈ B, ∀ b ∈ B, ¬ IsSquare (a + b)) :
    32 * B.card ≤ 11 * (u * v) := by
  let K := (33 * u) / 32
  have hpull : D * (crtImage huv B).card ≤ F.card * K := by
    apply uniform_relCover_transfer (SquareSumRel u) (SquareSumRel v) K3Rel
      hUniform hCover
    · intro A hA
      exact independent_card_le_of_coloring_bound htwo A hA
    · exact crtImage_independent huv B hB
  have hK : 32 * K ≤ 33 * u := by
    dsimp [K]
    omega
  have hmass : 3 * F.card = D * v := by
    simpa using three_mul_card_of_uniform hUniform
  rw [card_crtImage] at hpull
  exact cancel_cover_bound hD hpull hK hmass

private lemma twoPart_mul_oddPart (m : ℕ) :
    2 ^ m.factorization 2 * ordCompl[2] m = m := by
  exact Nat.ordProj_mul_ordCompl_eq_self m 2

private lemma twoPart_coprime_oddPart {m : ℕ} (hm : m ≠ 0) :
    Nat.Coprime (2 ^ m.factorization 2) (ordCompl[2] m) := by
  exact (Nat.coprime_ordCompl Nat.prime_two hm).pow_left _

private theorem los_modular_from_primary_inputs
    (hodd : ∀ (v : ℕ) [NeZero v], Odd v →
      ∃ D : ℕ, 0 < D ∧ ∃ F : Multiset (Fin 3 → ZMod v),
        UniformCover F D ∧ IsRelCover K3Rel (SquareSumRel v) F)
    (htwo : ∀ (j : ℕ) (F : ZMod (2 ^ j) → Finset (Fin 3)),
      (∀ x y, IsSquare (x + y) → ∀ c ∈ F x, ∀ d ∈ F y, c = d) →
      32 * ∑ x, (F x).card ≤ 33 * 2 ^ j)
    {m : ℕ} (hm : 1 ≤ m) (B : Finset (ZMod m))
    (hB : ∀ a ∈ B, ∀ b ∈ B, ¬ IsSquare (a + b)) :
    32 * B.card ≤ 11 * m := by
  let j := m.factorization 2
  let v := ordCompl[2] m
  have hm0 : m ≠ 0 := by omega
  have huv : Nat.Coprime (2 ^ j) v := by
    simpa [j, v] using twoPart_coprime_oddPart hm0
  have hv0 : v ≠ 0 := by
    exact (Nat.ordCompl_pos 2 hm0).ne'
  let _ : NeZero v := ⟨hv0⟩
  have hvodd : Odd v := (Nat.coprime_ordCompl Nat.prime_two hm0).odd_of_left
  obtain ⟨D, hD, F, hUniform, hCover⟩ := hodd v hvodd
  have hdecomp : 2 ^ j * v = m := by
    simpa [j, v] using twoPart_mul_oddPart m
  let e : ZMod m ≃+* ZMod (2 ^ j * v) := ZMod.ringEquivCongr hdecomp.symm
  let B' : Finset (ZMod (2 ^ j * v)) := B.image e
  have hB'_def : B' = B.image e := rfl
  have hcard : B'.card = B.card := by
    rw [hB'_def, Finset.card_image_iff.mpr]
    exact e.injective.injOn
  have hB' : ∀ a ∈ B', ∀ b ∈ B', ¬ IsSquare (a + b) := by
    intro a ha b hb hab
    rw [hB'_def, Finset.mem_image] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    apply hB x hx y hy
    rcases hab with ⟨z, hz⟩
    refine ⟨e.symm z, ?_⟩
    simpa using congrArg e.symm hz
  have hcore :=
    los_modular_of_uniform_odd_cover huv (htwo j) hD hUniform hCover B' hB'
  rwa [hcard, hdecomp] at hcore

/-- **Lagarias--Odlyzko--Shearer modular theorem.**  A subset of
`ZMod m` whose pairwise sums (including diagonal sums) avoid squares has
cardinality at most `11m/32`. -/
theorem los_modular {m : ℕ} (hm : 1 ≤ m) (B : Finset (ZMod m))
    (hB : ∀ a ∈ B, ∀ b ∈ B, ¬ IsSquare (a + b)) :
    32 * B.card ≤ 11 * m := by
  exact los_modular_from_primary_inputs odd_uniform_triangle_cover los_two_power hm B hB

end Erdos438
