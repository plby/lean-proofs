import ErdosProblems.Erdos360.Core

/-!
# GCD normalization for quotient--remainder product cores

This scratch module isolates the normalization needed before applying the
integer small-sumset estimates to the first-coordinate support of a partial
lift.  If every occupied first coordinate is divisible by `q`, division by
`q` is a Freiman isomorphism on the product core.  The final lemma pulls an
affine normalized fibre directly back to a cyclic coset progression; thus no
change of the ambient cyclic group is needed.
-/

namespace Erdos360

open scoped BigOperators Pointwise

attribute [local instance] Classical.propDecidable

/-- Divide the first coordinate of a quotient--remainder product point. -/
def divideFirstCoordinate {d : ℕ} (q : ℕ) (p : ℕ × ZMod d) :
    ℕ × ZMod d :=
  (p.1 / q, p.2)

/-- The product core obtained by dividing all first coordinates by `q`. -/
def normalizeFirstCoordinates {d : ℕ} (q : ℕ)
    (X : Finset (ℕ × ZMod d)) : Finset (ℕ × ZMod d) :=
  X.image (divideFirstCoordinate q)

lemma divideFirstCoordinate_injectiveOn
    {d q : ℕ} (hq : 0 < q) {X : Finset (ℕ × ZMod d)}
    (hdiv : ∀ p ∈ X, q ∣ p.1) :
    Set.InjOn (divideFirstCoordinate q) (X : Set (ℕ × ZMod d)) := by
  intro p hp r hr hpr
  apply Prod.ext
  · have hfirst : p.1 / q = r.1 / q := congrArg Prod.fst hpr
    calc
      p.1 = q * (p.1 / q) := (Nat.mul_div_cancel' (hdiv p hp)).symm
      _ = q * (r.1 / q) := by rw [hfirst]
      _ = r.1 := Nat.mul_div_cancel' (hdiv r hr)
  · simpa [divideFirstCoordinate] using congrArg Prod.snd hpr

lemma card_normalizeFirstCoordinates
    {d q : ℕ} (hq : 0 < q) {X : Finset (ℕ × ZMod d)}
    (hdiv : ∀ p ∈ X, q ∣ p.1) :
    (normalizeFirstCoordinates q X).card = X.card := by
  rw [normalizeFirstCoordinates, Finset.card_image_iff.mpr]
  intro p hp r hr hpr
  exact divideFirstCoordinate_injectiveOn hq hdiv hp hr hpr

lemma divideFirstCoordinate_add_of_dvd
    {d q : ℕ} (p r : ℕ × ZMod d) (hp : q ∣ p.1) (hr : q ∣ r.1) :
    divideFirstCoordinate q (p + r) =
      divideFirstCoordinate q p + divideFirstCoordinate q r := by
  apply Prod.ext
  · exact Nat.add_div_of_dvd_right hp
  · rfl

lemma normalizeFirstCoordinates_add
    {d q : ℕ} (X Y : Finset (ℕ × ZMod d))
    (hX : ∀ p ∈ X, q ∣ p.1) (hY : ∀ p ∈ Y, q ∣ p.1) :
    normalizeFirstCoordinates q (X + Y) =
      normalizeFirstCoordinates q X + normalizeFirstCoordinates q Y := by
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hz
    obtain ⟨p, hp, r, hr, hpr⟩ := Finset.mem_add.mp hw
    subst w
    rw [divideFirstCoordinate_add_of_dvd p r (hX p hp) (hY r hr)] at hwz
    rw [← hwz]
    exact Finset.add_mem_add
      (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
      (Finset.mem_image.mpr ⟨r, hr, rfl⟩)
  · intro hz
    obtain ⟨p', hp', r', hr', hsum⟩ := Finset.mem_add.mp hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hp'
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hr'
    apply Finset.mem_image.mpr
    refine ⟨p + r, Finset.add_mem_add hp hr, ?_⟩
    rw [divideFirstCoordinate_add_of_dvd p r (hX p hp) (hY r hr)]
    exact hsum

lemma firstCoordinate_divisible_on_add
    {d q : ℕ} {X Y : Finset (ℕ × ZMod d)}
    (hX : ∀ p ∈ X, q ∣ p.1) (hY : ∀ p ∈ Y, q ∣ p.1) :
    ∀ p ∈ X + Y, q ∣ p.1 := by
  intro p hp
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hp
  exact dvd_add (hX x hx) (hY y hy)

lemma card_normalizeFirstCoordinates_add
    {d q : ℕ} (hq : 0 < q) {X Y : Finset (ℕ × ZMod d)}
    (hX : ∀ p ∈ X, q ∣ p.1) (hY : ∀ p ∈ Y, q ∣ p.1) :
    (normalizeFirstCoordinates q X + normalizeFirstCoordinates q Y).card =
      (X + Y).card := by
  rw [← normalizeFirstCoordinates_add X Y hX hY]
  exact card_normalizeFirstCoordinates hq (firstCoordinate_divisible_on_add hX hY)

lemma firstCoordinateSet_normalizeFirstCoordinates
    {d q : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d)) :
    firstCoordinateSet (normalizeFirstCoordinates q X) =
      (firstCoordinateSet X).image (fun a ↦ a / q) := by
  ext a
  simp only [firstCoordinateSet, normalizeFirstCoordinates,
    divideFirstCoordinate, Finset.mem_image, Prod.exists]
  aesop

lemma card_firstCoordinateSet_normalizeFirstCoordinates
    {d q : ℕ} [NeZero d] (hq : 0 < q)
    {X : Finset (ℕ × ZMod d)}
    (hdiv : ∀ p ∈ X, q ∣ p.1) :
    (firstCoordinateSet (normalizeFirstCoordinates q X)).card =
      (firstCoordinateSet X).card := by
  rw [firstCoordinateSet_normalizeFirstCoordinates,
    Finset.card_image_iff.mpr]
  intro a ha b hb hab
  have haDiv : q ∣ a := by
    obtain ⟨y, hy⟩ := mem_firstCoordinateSet.mp ha
    exact hdiv (a, y) hy
  have hbDiv : q ∣ b := by
    obtain ⟨y, hy⟩ := mem_firstCoordinateSet.mp hb
    exact hdiv (b, y) hy
  change a / q = b / q at hab
  calc
    a = q * (a / q) := (Nat.mul_div_cancel' haDiv).symm
    _ = q * (b / q) := by rw [hab]
    _ = b := Nat.mul_div_cancel' hbDiv

/-- Normalization does not merge fibres when every occupied coordinate is
divisible by the normalization factor. -/
lemma coordinateFiber_normalizeFirstCoordinates
    {d q : ℕ} [NeZero d] {X : Finset (ℕ × ZMod d)}
    (hdiv : ∀ p ∈ X, q ∣ p.1) {a : ℕ}
    (ha : a ∈ firstCoordinateSet X) :
    coordinateFiber (normalizeFirstCoordinates q X) (a / q) =
      coordinateFiber X a := by
  ext y
  simp only [mem_coordinateFiber, normalizeFirstCoordinates,
    Finset.mem_image]
  constructor
  · rintro ⟨p, hp, hpy⟩
    have hfirst : p.1 / q = a / q := congrArg Prod.fst hpy
    have haDiv : q ∣ a := by
      obtain ⟨z, hz⟩ := mem_firstCoordinateSet.mp ha
      exact hdiv (a, z) hz
    have heq : p.1 = a := by
      calc
        p.1 = q * (p.1 / q) := (Nat.mul_div_cancel' (hdiv p hp)).symm
        _ = q * (a / q) := by rw [hfirst]
        _ = a := Nat.mul_div_cancel' haDiv
    have hsnd : p.2 = y := congrArg Prod.snd hpy
    have hpEq : p = (a, y) := Prod.ext heq hsnd
    rwa [← hpEq]
  · intro hay
    exact ⟨(a, y), hay, rfl⟩

/-- Dividing a no-carry core by `q` changes the no-carry threshold from
`m` to `m/q`. -/
lemma normalizeFirstCoordinates_noCarry
    {d m q : ℕ} (hq : 0 < q) (hqm : q ∣ m)
    {X : Finset (ℕ × ZMod d)}
    (hdiv : ∀ p ∈ X, q ∣ p.1)
    (hnowrap : ∀ p ∈ X, ∀ r ∈ X, p.1 + r.1 < m) :
    ∀ p ∈ normalizeFirstCoordinates q X,
      ∀ r ∈ normalizeFirstCoordinates q X, p.1 + r.1 < m / q := by
  intro p hp r hr
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hr
  have hsumDiv : q ∣ x.1 + y.1 := dvd_add (hdiv x hx) (hdiv y hy)
  have hlt : (x.1 + y.1) / q < m / q :=
    (Nat.div_lt_div_right hq.ne' hsumDiv hqm).mpr (hnowrap x hx y hy)
  simpa [divideFirstCoordinate, Nat.add_div_of_dvd_right (hdiv x hx)] using hlt

lemma gcd_dvd_firstCoordinate
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d)) :
    ∀ p ∈ X, (firstCoordinateSet X).gcd (fun a : ℕ ↦ a) ∣ p.1 := by
  intro p hp
  exact Finset.gcd_dvd (mem_firstCoordinateSet.mpr ⟨p.2, hp⟩)

lemma zmodQuotRemImage_firstCoordinate_divisible
    {m d q : ℕ} [NeZero d] [NeZero (m * d)]
    {B : Finset (ZMod (m * d))}
    (hdiv : ∀ z ∈ B, q ∣ z.val % m) :
    ∀ p ∈ zmodQuotRemImage m d B, q ∣ p.1 := by
  intro p hp
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
  exact hdiv z hz

/-- Dividing the first support by its (positive) gcd yields gcd one. -/
lemma gcd_firstCoordinateSet_normalizeFirstCoordinates
    {d : ℕ} [NeZero d] {X : Finset (ℕ × ZMod d)}
    (_hX : X.Nonempty)
    (hq : 0 < (firstCoordinateSet X).gcd (fun a : ℕ ↦ a)) :
    (firstCoordinateSet
        (normalizeFirstCoordinates
          ((firstCoordinateSet X).gcd (fun a : ℕ ↦ a)) X)).gcd
      (fun a : ℕ ↦ a) = 1 := by
  let q := (firstCoordinateSet X).gcd (fun a : ℕ ↦ a)
  have hqne : q ≠ 0 := Nat.ne_of_gt hq
  have haExists : ∃ a ∈ firstCoordinateSet X, a ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    have hzero : q = 0 := Finset.gcd_eq_zero_iff.mpr hnone
    exact hqne hzero
  obtain ⟨a, ha, hane⟩ := haExists
  rw [firstCoordinateSet_normalizeFirstCoordinates, Finset.gcd_image]
  exact Finset.gcd_div_id_eq_one ha hane

/-- The integral gcd used by the Hall/Ruzsa lemmas is also normalized. -/
lemma intGcd_firstCoordinateSet_normalizeFirstCoordinates
    {d : ℕ} [NeZero d] {X : Finset (ℕ × ZMod d)}
    (hX : X.Nonempty)
    (hq : 0 < (firstCoordinateSet X).gcd (fun a : ℕ ↦ a)) :
    (firstCoordinateSet
        (normalizeFirstCoordinates
          ((firstCoordinateSet X).gcd (fun a : ℕ ↦ a)) X)).gcd
      (fun a ↦ (a : ℤ)) = 1 := by
  rw [Erdos13Additive.nat_int_finset_gcd,
    gcd_firstCoordinateSet_normalizeFirstCoordinates hX hq]
  norm_num

/-- Pull an affine fibre in gcd-normalized first coordinates back to the
original cyclic group.  The normalized unit step becomes the original step
`q + m*x`. -/
lemma zmodQuotRem_normalizedAffineFiber_subset_cyclicCosetProgression
    {m d q L : ℕ} [NeZero d] [NeZero (m * d)]
    (hq : 0 < q) {K : AddSubgroup (ZMod d)} {x y : ZMod d}
    {D : Finset (ZMod (m * d))}
    (hD : ∀ z ∈ D,
      q ∣ z.val % m ∧
      (z.val % m) / q < L ∧
      (z.val / m : ZMod d) - (((z.val % m) / q) • x + y) ∈ K) :
    D ⊆ cyclicCosetProgression
      (K.map (zmodQuotientEmbedding m d))
      (zmodQuotientEmbedding m d y)
      ((q : ZMod (m * d)) + zmodQuotientEmbedding m d x) L := by
  intro z hz
  obtain ⟨hqrem, hrange, hk⟩ := hD z hz
  apply mem_cyclicCosetProgression_iff.mpr
  refine ⟨(z.val % m) / q, hrange, ?_⟩
  apply AddSubgroup.mem_map.mpr
  refine ⟨(z.val / m : ZMod d) - (((z.val % m) / q) • x + y), hk, ?_⟩
  rw [map_sub, map_add, map_nsmul]
  have hzrec := zmodQuotientEmbedding_quotient_add_remainder
    (m := m) (d := d) z
  have hqmul : q * ((z.val % m) / q) = z.val % m := by
    exact Nat.mul_div_cancel' hqrem
  have hcast : (z.val % m : ZMod (m * d)) =
      ((z.val % m) / q) • (q : ZMod (m * d)) := by
    simp only [nsmul_eq_mul]
    rw [← Nat.cast_mul]
    congr 1
    exact hqmul.symm.trans (Nat.mul_comm q ((z.val % m) / q))
  calc
    zmodQuotientEmbedding m d (z.val / m : ZMod d) -
          (((z.val % m) / q) • zmodQuotientEmbedding m d x +
            zmodQuotientEmbedding m d y) =
        (zmodQuotientEmbedding m d (z.val / m : ZMod d) +
            (z.val % m : ZMod (m * d))) -
          (zmodQuotientEmbedding m d y + ((z.val % m) / q) •
            ((q : ZMod (m * d)) + zmodQuotientEmbedding m d x)) := by
      rw [hcast]
      ring
    _ = z - (zmodQuotientEmbedding m d y + ((z.val % m) / q) •
          ((q : ZMod (m * d)) + zmodQuotientEmbedding m d x)) := by
      rw [hzrec]

/-- The normalized affine pullback immediately supplies the ordinary long
progression cover used by the modular subset-sum sieve. -/
lemma zmodQuotRem_normalizedAffineFiber_shifted_longProgressionCover
    {m d q L : ℕ} [NeZero d] [NeZero (m * d)]
    (hq : 0 < q) (hL : 0 < L)
    {K : AddSubgroup (ZMod d)} {x y : ZMod d}
    {D : Finset (ZMod (m * d))}
    (hD : ∀ z ∈ D,
      q ∣ z.val % m ∧
      (z.val % m) / q < L ∧
      (z.val / m : ZMod d) - (((z.val % m) / q) • x + y) ∈ K) :
    HasLongProgressionCover (shiftedZmodValues D)
      (6 * (L * Nat.card (K.map (zmodQuotientEmbedding m d)))) := by
  let H := K.map (zmodQuotientEmbedding m d)
  let a := zmodQuotientEmbedding m d y
  let step := (q : ZMod (m * d)) + zmodQuotientEmbedding m d x
  have hsub : D ⊆ cyclicCosetProgression H a step L := by
    exact zmodQuotRem_normalizedAffineFiber_subset_cyclicCosetProgression
      hq hD
  have hb : 0 < m * d := Nat.pos_of_ne_zero (NeZero.ne (m * d))
  obtain ⟨gen, hgen, hgenDiv, hHdiv, hmult⟩ :=
    exists_generator_modulus hb H
  have hcover :=
    cyclicCosetProgression_shifted_longProgressionCover_parametric
      hb hgen hgenDiv hL H hHdiv hmult a step
  exact hcover.mono_set (shiftedZmodValues_mono hsub)

end Erdos360
