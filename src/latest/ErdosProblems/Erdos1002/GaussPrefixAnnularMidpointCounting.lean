import ErdosProblems.Erdos1002.GaussPrefixAnnularTimeZeroMode

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Thin moving midpoint bands

For the early/late Fourier dichotomy, a later zero-mode depth is discarded
when it lies in a thin band around a midpoint depending on the last
nonzero depth.  This file supplies the exact finite coding estimate: after
all coordinates except the band coordinate are recorded, its signed
distance from the moving center has fewer than `W` possibilities.
-/

open Finset
open scoped BigOperators

namespace Erdos1002

noncomputable section

local instance midpointCountingPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

def midpointBandNatTupleFamily
    {r : ℕ} (centerIndex bandIndex : Fin r)
    (H W : ℕ) (tuples : Finset (Fin r → ℕ)) :
    Finset (Fin r → ℕ) :=
  tuples.filter fun t ↦
    Nat.dist (2 * t bandIndex) (H + t centerIndex) < W

@[simp] theorem mem_midpointBandNatTupleFamily_iff
    {r H W : ℕ} {centerIndex bandIndex : Fin r}
    {tuples : Finset (Fin r → ℕ)} {t : Fin r → ℕ} :
    t ∈ midpointBandNatTupleFamily centerIndex bandIndex H W tuples ↔
      t ∈ tuples ∧
        Nat.dist (2 * t bandIndex) (H + t centerIndex) < W := by
  simp [midpointBandNatTupleFamily]

/-- A single moving midpoint band costs one ambient coordinate. -/
theorem card_midpointBandNatTupleFamily_le_of_bounded
    {r H W : ℕ} (centerIndex bandIndex : Fin r)
    (hne : bandIndex ≠ centerIndex)
    (tuples : Finset (Fin r → ℕ))
    (hbound : ∀ t ∈ tuples, ∀ i, t i < H) :
    (midpointBandNatTupleFamily
        centerIndex bandIndex H W tuples).card ≤
      (2 * W) * H ^ (r - 1) := by
  let family :=
    midpointBandNatTupleFamily centerIndex bandIndex H W tuples
  let signedOffset (u : ↥family) : Sum (Fin W) (Fin W) :=
    if hle : 2 * u.1 bandIndex ≤ H + u.1 centerIndex then
      Sum.inl
        ⟨(H + u.1 centerIndex) - 2 * u.1 bandIndex, by
          have hu :=
            (mem_midpointBandNatTupleFamily_iff.mp u.2).2
          rw [Nat.dist_eq_sub_of_le hle] at hu
          exact hu⟩
    else
      Sum.inr
        ⟨2 * u.1 bandIndex - (H + u.1 centerIndex), by
          have hu :=
            (mem_midpointBandNatTupleFamily_iff.mp u.2).2
          rw [Nat.dist_eq_sub_of_le_right (Nat.le_of_not_ge hle)] at hu
          exact hu⟩
  let otherCoordinates (u : ↥family) :
      {i : Fin r // i ≠ bandIndex} → Fin H :=
    fun i ↦
      ⟨u.1 i.1,
        hbound u.1
          (mem_midpointBandNatTupleFamily_iff.mp u.2).1 i.1⟩
  let code (u : ↥family) :
      Sum (Fin W) (Fin W) ×
        ({i : Fin r // i ≠ bandIndex} → Fin H) :=
    (signedOffset u, otherCoordinates u)
  let decodeOffset : Sum (Fin W) (Fin W) → ℤ
    | Sum.inl d => -(d.1 : ℤ)
    | Sum.inr d => (d.1 : ℤ)
  have hdecode (u : ↥family) :
      decodeOffset (signedOffset u) =
        ((2 * u.1 bandIndex : ℕ) : ℤ) -
          ((H + u.1 centerIndex : ℕ) : ℤ) := by
    dsimp only [decodeOffset, signedOffset]
    split_ifs with hle
    · simp only
      omega
    · simp only
      omega
  have hinjective : Function.Injective code := by
    intro u v huv
    have hother : otherCoordinates u = otherCoordinates v :=
      congrArg Prod.snd huv
    have hcenter : u.1 centerIndex = v.1 centerIndex := by
      have hcne : centerIndex ≠ bandIndex := fun h ↦ hne h.symm
      exact congrArg Fin.val (congrFun hother ⟨centerIndex, hcne⟩)
    have hoffset : signedOffset u = signedOffset v :=
      congrArg Prod.fst huv
    have hband : u.1 bandIndex = v.1 bandIndex := by
      have hd := congrArg decodeOffset hoffset
      rw [hdecode u, hdecode v] at hd
      omega
    apply Subtype.ext
    funext i
    by_cases hi : i = bandIndex
    · simpa only [hi] using! hband
    · exact congrArg Fin.val (congrFun hother ⟨i, hi⟩)
  calc
    (midpointBandNatTupleFamily
        centerIndex bandIndex H W tuples).card =
        Fintype.card (↥family) := by
      symm
      exact Fintype.card_coe _
    _ ≤ Fintype.card
        (Sum (Fin W) (Fin W) ×
          ({i : Fin r // i ≠ bandIndex} → Fin H)) :=
      Fintype.card_le_of_injective code hinjective
    _ = (2 * W) * H ^ (r - 1) := by
      simp [Fintype.card_subtype_compl, two_mul]

end

end Erdos1002
