/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Elementary finite Bohr-set calculus

This file supplies the algebraic and finite-cardinality part of the Bohr-set
technology used in the proof of Erdős Problem 140.  A frequency is an additive
character with values in `ℝ / ℤ`, represented by `AddCircle 1`.  Widths are
nonnegative reals.  Keeping the frequency set separate from the width function
is useful: dilation never changes the rank, even at scale zero.

The final theorem is a general volumetric lower bound.  A finite quantization
of every circle coordinate into cells of diameter at most the corresponding
width gives

`|G| ≤ (product of the numbers of cells) * |B|`.

Thus a uniform `m`-cell quantization gives the familiar `|G| ≤ m^rank |B|`.
The theorem is stated with arbitrary quantizers so that later analytic files
can choose the most convenient short-arc partition.
-/

open scoped BigOperators

namespace Erdos140

open Finset

/-- An additive character of `G`, with the target normalized as `ℝ / ℤ`. -/
abbrev AddCharacter (G : Type*) [AddCommGroup G] := G →+ AddCircle (1 : ℝ)

/-- Finite Bohr data: finitely many additive characters and one nonnegative
width for each character.  Widths away from `freq` are irrelevant. -/
structure BohrData (G : Type*) [AddCommGroup G] where
  freq : Finset (AddCharacter G)
  width : AddCharacter G → NNReal

namespace BohrData

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-- The rank of a Bohr datum is the number of its frequencies. -/
def rank (B : BohrData G) : ℕ := B.freq.card

/-- Scalar dilation multiplies all widths and leaves the frequency set fixed. -/
def dilate (B : BohrData G) (t : NNReal) : BohrData G where
  freq := B.freq
  width γ := t * B.width γ

@[simp] lemma freq_dilate (B : BohrData G) (t : NNReal) :
    (B.dilate t).freq = B.freq := rfl

@[simp] lemma width_dilate (B : BohrData G) (t : NNReal) (γ : AddCharacter G) :
    (B.dilate t).width γ = t * B.width γ := rfl

@[simp] lemma rank_dilate (B : BohrData G) (t : NNReal) :
    (B.dilate t).rank = B.rank := rfl

@[simp] lemma dilate_one (B : BohrData G) : B.dilate 1 = B := by
  cases B
  simp [dilate]

@[simp] lemma dilate_dilate (B : BohrData G) (s t : NNReal) :
    (B.dilate s).dilate t = B.dilate (t * s) := by
  cases B
  simp [dilate, mul_assoc]

/-- The finite carrier of a Bohr datum. -/
noncomputable def carrier [Fintype G] (B : BohrData G) : Finset G := by
  classical
  exact Finset.univ.filter fun x ↦
    ∀ γ ∈ B.freq, ‖γ x‖ ≤ (B.width γ : ℝ)

@[simp] lemma mem_carrier [Fintype G] (B : BohrData G) (x : G) :
    x ∈ B.carrier ↔ ∀ γ ∈ B.freq, ‖γ x‖ ≤ (B.width γ : ℝ) := by
  classical
  simp [carrier]

lemma zero_mem_carrier [Fintype G] (B : BohrData G) : 0 ∈ B.carrier := by
  rw [mem_carrier]
  intro γ hγ
  simp

lemma carrier_nonempty [Fintype G] (B : BohrData G) : B.carrier.Nonempty :=
  ⟨0, B.zero_mem_carrier⟩

lemma one_le_card_carrier [Fintype G] (B : BohrData G) : 1 ≤ B.carrier.card :=
  Finset.one_le_card.mpr B.carrier_nonempty

lemma neg_mem_carrier [Fintype G] {B : BohrData G} {x : G} :
    -x ∈ B.carrier ↔ x ∈ B.carrier := by
  simp only [mem_carrier]
  constructor <;> intro hx γ hγ
  · simpa only [map_neg, norm_neg] using hx γ hγ
  · simpa only [map_neg, norm_neg] using hx γ hγ

/-- Inclusion under dilation by a larger nonnegative scalar. -/
lemma carrier_dilate_mono [Fintype G] {B : BohrData G} {s t : NNReal} (hst : s ≤ t) :
    (B.dilate s).carrier ⊆ (B.dilate t).carrier := by
  intro x hx
  rw [mem_carrier] at hx ⊢
  intro γ hγ
  have hwidth : (s : ℝ) * (B.width γ : ℝ) ≤
      (t : ℝ) * (B.width γ : ℝ) := by
    gcongr
  exact (hx γ hγ).trans hwidth

/-- The triangle inequality for two (possibly differently) dilated Bohr sets. -/
lemma add_mem_dilate [Fintype G] {B : BohrData G} {s t : NNReal} {x y : G}
    (hx : x ∈ (B.dilate s).carrier) (hy : y ∈ (B.dilate t).carrier) :
    x + y ∈ (B.dilate (s + t)).carrier := by
  rw [mem_carrier] at hx hy ⊢
  intro γ hγ
  rw [map_add]
  calc
    ‖γ x + γ y‖ ≤ ‖γ x‖ + ‖γ y‖ := norm_add_le _ _
    _ ≤ (s : ℝ) * (B.width γ : ℝ) + (t : ℝ) * (B.width γ : ℝ) :=
      add_le_add (hx γ hγ) (hy γ hγ)
    _ = ((s + t : NNReal) : ℝ) * (B.width γ : ℝ) := by
      push_cast
      ring

/-- The subtraction form of the Bohr triangle inequality. -/
lemma sub_mem_dilate [Fintype G] {B : BohrData G} {s t : NNReal} {x y : G}
    (hx : x ∈ (B.dilate s).carrier) (hy : y ∈ (B.dilate t).carrier) :
    x - y ∈ (B.dilate (s + t)).carrier := by
  rw [sub_eq_add_neg]
  exact add_mem_dilate hx (neg_mem_carrier.mpr hy)

/-- Transport Bohr data through an additive equivalence.  Frequencies are
pulled back along the inverse equivalence. -/
noncomputable def map (B : BohrData G) (e : G ≃+ H) : BohrData H := by
  classical
  exact
    { freq := B.freq.image fun γ ↦ γ.comp e.symm.toAddMonoidHom
      width := fun δ ↦ B.width (δ.comp e.toAddMonoidHom) }

@[simp] lemma width_map (B : BohrData G) (e : G ≃+ H) (δ : AddCharacter H) :
    (B.map e).width δ = B.width (δ.comp e.toAddMonoidHom) := by
  classical
  simp [map]

@[simp] lemma mem_freq_map (B : BohrData G) (e : G ≃+ H) (δ : AddCharacter H) :
    δ ∈ (B.map e).freq ↔
      ∃ γ ∈ B.freq, γ.comp e.symm.toAddMonoidHom = δ := by
  classical
  simp [map]

private lemma comp_symm_injective (e : G ≃+ H) :
    Function.Injective (fun γ : AddCharacter G ↦ γ.comp e.symm.toAddMonoidHom) := by
  intro γ δ h
  ext x
  have hx := DFunLike.congr_fun h (e x)
  simpa using hx

@[simp] lemma rank_map (B : BohrData G) (e : G ≃+ H) :
    (B.map e).rank = B.rank := by
  classical
  rw [rank, rank, map]
  exact Finset.card_image_iff.mpr (comp_symm_injective e).injOn

private lemma width_map_of_mem (B : BohrData G) (e : G ≃+ H)
    (γ : AddCharacter G) :
    (B.map e).width (γ.comp e.symm.toAddMonoidHom) = B.width γ := by
  change B.width ((γ.comp e.symm.toAddMonoidHom).comp e.toAddMonoidHom) = B.width γ
  apply congrArg B.width
  ext x
  simp

/-- An equivalence maps the old carrier exactly onto the transported carrier. -/
@[simp] lemma mem_map_carrier [Fintype G] [Fintype H]
    (B : BohrData G) (e : G ≃+ H) (x : G) :
    e x ∈ (B.map e).carrier ↔ x ∈ B.carrier := by
  classical
  rw [mem_carrier, mem_carrier]
  constructor
  · intro hx γ hγ
    have hfreq : γ.comp e.symm.toAddMonoidHom ∈ (B.map e).freq := by
      exact mem_freq_map B e _ |>.mpr ⟨γ, hγ, rfl⟩
    have hh := hx (γ.comp e.symm.toAddMonoidHom) hfreq
    rw [width_map_of_mem] at hh
    have happ : (γ.comp e.symm.toAddMonoidHom) (e x) = γ x := by simp
    rwa [happ] at hh
  · intro hx δ hδ
    rcases (mem_freq_map B e δ).mp hδ with ⟨γ, hγ, rfl⟩
    rw [width_map_of_mem]
    have happ : (γ.comp e.symm.toAddMonoidHom) (e x) = γ x := by simp
    rw [happ]
    exact hx γ hγ

/-- Transport by an additive equivalence preserves Bohr cardinality. -/
@[simp] lemma card_map_carrier [Fintype G] [Fintype H]
    (B : BohrData G) (e : G ≃+ H) :
    (B.map e).carrier.card = B.carrier.card := by
  classical
  symm
  apply Finset.card_bijective e e.bijective
  intro x
  exact (mem_map_carrier B e x).symm

/-! ### The doubling automorphism of an odd cyclic group -/

/-- Multiplication by two is an additive automorphism of `ZMod N` when `N` is
odd.  It is written additively as `x ↦ x + x`, which is the form used in
three-term-progression arguments. -/
noncomputable def zmodDoublingEquiv (N : ℕ) (hN : Odd N) : ZMod N ≃+ ZMod N := by
  let f : ZMod N →+ ZMod N :=
    { toFun := fun x ↦ x + x
      map_zero' := by simp
      map_add' := by
        intro x y
        abel }
  have hunit : IsUnit (2 : ZMod N) :=
    (ZMod.isUnit_iff_coprime 2 N).2 (Nat.coprime_two_left.mpr hN)
  have hbijMul : Function.Bijective (fun x : ZMod N ↦ (2 : ZMod N) * x) :=
    IsUnit.isUnit_iff_mulLeft_bijective.mp hunit
  have hbij : Function.Bijective f := by
    simpa only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, two_mul] using hbijMul
  exact AddEquiv.ofBijective f hbij

@[simp] lemma zmodDoublingEquiv_apply (N : ℕ) (hN : Odd N) (x : ZMod N) :
    zmodDoublingEquiv N hN x = x + x := by
  simp [zmodDoublingEquiv]

@[simp] lemma rank_map_zmodDoubling (N : ℕ) (hN : Odd N) (B : BohrData (ZMod N)) :
    (B.map (zmodDoublingEquiv N hN)).rank = B.rank :=
  rank_map B (zmodDoublingEquiv N hN)

@[simp] lemma card_map_zmodDoubling (N : ℕ) [NeZero N] (hN : Odd N)
    (B : BohrData (ZMod N)) :
    (B.map (zmodDoublingEquiv N hN)).carrier.card = B.carrier.card :=
  card_map_carrier B (zmodDoublingEquiv N hN)

/-! ## A finite volumetric lower bound -/

/-- The simultaneous finite signature attached to per-frequency quantizers. -/
def signature (B : BohrData G)
    (cells : B.freq → ℕ)
    (quantize : ∀ γ : B.freq, AddCircle (1 : ℝ) → Fin (cells γ))
    (x : G) : ∀ γ : B.freq, Fin (cells γ) :=
  fun γ ↦ quantize γ (γ.1 x)

/-- A fiber of a short-cell signature injects into the Bohr carrier by subtracting
any fixed point of the fiber. -/
private lemma card_signature_fiber_le [Fintype G]
    (B : BohrData G)
    (cells : B.freq → ℕ)
    (quantize : ∀ γ : B.freq, AddCircle (1 : ℝ) → Fin (cells γ))
    (hshort : ∀ (γ : B.freq) (z w : AddCircle (1 : ℝ)),
      quantize γ z = quantize γ w → ‖z - w‖ ≤ (B.width γ.1 : ℝ))
    (a : ∀ γ : B.freq, Fin (cells γ)) :
    Fintype.card {x : G // B.signature cells quantize x = a} ≤ B.carrier.card := by
  classical
  by_cases hfiber : Nonempty {x : G // B.signature cells quantize x = a}
  · let x₀ : {x : G // B.signature cells quantize x = a} := Classical.choice hfiber
    let f : {x : G // B.signature cells quantize x = a} → {x // x ∈ B.carrier} :=
      fun x ↦ ⟨x.1 - x₀.1, by
        rw [mem_carrier]
        intro γ hγ
        have hsig : B.signature cells quantize x.1 =
            B.signature cells quantize x₀.1 := x.2.trans x₀.2.symm
        have hcoord := congrFun hsig ⟨γ, hγ⟩
        rw [map_sub]
        exact hshort ⟨γ, hγ⟩ (γ x.1) (γ x₀.1) hcoord⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      have hval := congr_arg Subtype.val hxy
      dsimp [f] at hval
      exact sub_left_injective hval
    calc
      Fintype.card {x : G // B.signature cells quantize x = a} ≤
          Fintype.card {x // x ∈ B.carrier} := Fintype.card_le_of_injective f hf
      _ = B.carrier.card := Fintype.card_coe B.carrier
  · simp only [not_nonempty_iff] at hfiber
    simp

/-- **Finite Bohr volumetric bound.** If coordinate `γ` is quantized into
`cells γ` cells, and points in one cell differ by at most the width of `γ`, then
the product of the cell counts times the Bohr cardinality covers the whole
group cardinality. -/
theorem card_le_prod_mul_card [Fintype G]
    (B : BohrData G)
    (cells : B.freq → ℕ)
    (quantize : ∀ γ : B.freq, AddCircle (1 : ℝ) → Fin (cells γ))
    (hshort : ∀ (γ : B.freq) (z w : AddCircle (1 : ℝ)),
      quantize γ z = quantize γ w → ‖z - w‖ ≤ (B.width γ.1 : ℝ)) :
    Fintype.card G ≤ (∏ γ : B.freq, cells γ) * B.carrier.card := by
  classical
  let S := ∀ γ : B.freq, Fin (cells γ)
  let q : G → S := B.signature cells quantize
  have hfiber : ∀ a : S, Fintype.card {x : G // q x = a} ≤ B.carrier.card := by
    intro a
    exact card_signature_fiber_le B cells quantize hshort a
  have hcardS : Fintype.card S = ∏ γ : B.freq, cells γ := by
    dsimp [S]
    rw [Fintype.card_pi]
    simp
  rw [← hcardS]
  by_contra h
  have hlt : Fintype.card S * B.carrier.card < Fintype.card G := by omega
  obtain ⟨a, ha⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card (f := q) hlt
  have hfa : #{x | q x = a} ≤ B.carrier.card := by
    rw [← Fintype.card_subtype]
    exact hfiber a
  exact (not_lt_of_ge hfa) ha

/-- Uniform-cell specialization of `card_le_prod_mul_card`. -/
theorem card_le_pow_rank_mul_card [Fintype G]
    (B : BohrData G) (m : ℕ)
    (quantize : ∀ _γ : B.freq, AddCircle (1 : ℝ) → Fin m)
    (hshort : ∀ (γ : B.freq) (z w : AddCircle (1 : ℝ)),
      quantize γ z = quantize γ w → ‖z - w‖ ≤ (B.width γ.1 : ℝ)) :
    Fintype.card G ≤ m ^ B.rank * B.carrier.card := by
  simpa [rank] using
    card_le_prod_mul_card B (fun _ ↦ m) quantize hshort

end BohrData

end Erdos140

#print axioms Erdos140.BohrData.card_le_pow_rank_mul_card
