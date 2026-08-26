import Mathlib
import ErdosProblems.Erdos336.ParentSyndetic
import ErdosProblems.Erdos336.SyndeticDenseReflection
import ErdosProblems.Erdos336.CyclicIntegerLift
import ErdosProblems.Erdos336.ReflectedBogolyubovBridge

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Local bounded-dimensional Bohr patterns from a syndetic exact power
-/

namespace Erdos336

open scoped BigOperators

lemma stdAddChar_int_zsmul_toAddCircle
    {N : ℕ} [NeZero N] (x : ℤ) (k : ZMod N) :
    ((AddCircle.toCircle (x • ZMod.toAddCircle k) : Circle) : ℂ) =
      ZMod.stdAddChar ((x : ZMod N) * k) := by
  rw [ZMod.stdAddChar_apply]
  norm_cast
  change AddCircle.toCircle (x • ZMod.toAddCircle k) =
    AddCircle.toCircle (ZMod.toAddCircle ((x : ZMod N) * k))
  congr 1
  rw [← AddMonoidHom.map_zsmul ZMod.toAddCircle x k]
  congr 1
  simp [zsmul_eq_mul]

/-- Pad an enumeration of a finset to any larger positive `Fin d`. -/
theorem exists_padded_enumeration {α : Type*} [DecidableEq α] [Inhabited α]
    (Γ : Finset α) {d : ℕ} (hd : 0 < d) (hcard : Γ.card ≤ d) :
    ∃ e : Fin d → α, ∀ k ∈ Γ, ∃ j : Fin d, e j = k := by
  let e : Fin d → α := fun j =>
    if hj : j.val < Γ.card then
      ((Γ.equivFin).symm ⟨j.val, hj⟩).val
    else default
  refine ⟨e, ?_⟩
  intro k hk
  let i : Fin Γ.card := Γ.equivFin ⟨k, hk⟩
  let j : Fin d := Fin.castLE hcard i
  refine ⟨j, ?_⟩
  have hjlt : j.val < Γ.card := i.isLt
  simp only [e, dif_pos hjlt, j]
  exact congrArg Subtype.val ((Γ.equivFin).symm_apply_apply ⟨k, hk⟩)

/-- The quantitative local datum needed for compactness. Every centered radius
has a translate of a Bohr pattern, in a fixed dimension depending only on the
number of syndetic shifts, inside the exact `4h`-power. -/
theorem exists_local_bohr_data_of_exactPowerEventuallySyndetic
    {D : Set ℤ} {c : ℤ} {h : ℕ}
    (hsynd : ExactPowerEventuallySyndetic D c h) :
    let s := h + 1
    let q := 4 * s ^ 2
    let d := 16 * q ^ 3
    ∀ R : ℕ, ∃ θ : Fin d → AddCircle (1 : ℝ), ∃ center : ℤ,
      ∀ x : ℤ, x.natAbs ≤ R →
        (∀ j : Fin d,
          ‖((AddCircle.toCircle (x • θ j) : Circle) : ℂ) - 1‖ ≤
            (1 / 2 : ℝ)) →
        ZRepExactly D (4 * h) (center + x) := by
  dsimp only
  intro R
  classical
  obtain ⟨N₀, htail⟩ := hsynd
  let s : ℕ := h + 1
  let q : ℕ := 4 * s ^ 2
  let d : ℕ := 16 * q ^ 3
  let T : ℕ := R + 1
  let len : ℕ := s ^ 2 * T
  let F : Finset ℤ := (Finset.range s).image fun j : ℕ => (j : ℤ) * c
  let J : Finset ℤ := Finset.Ico N₀ (N₀ + (len : ℤ))
  let S : Set ℤ := {n | ZRepExactly D h n}
  have hspos : 0 < s := by simp [s]
  have hTpos : 0 < T := by simp [T]
  have hlenpos : 0 < len := by
    dsimp [len]
    positivity
  have hFne : F.Nonempty := by
    refine ⟨0, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨0, ?_, by simp⟩
    simp [s]
  have hFcard : F.card ≤ s := by
    simpa [F] using
      (Finset.card_image_le (s := Finset.range s)
        (f := fun j : ℕ => (j : ℤ) * c))
  have hcoverJ : ∀ n ∈ J, ∃ f ∈ F, n - f ∈ S := by
    intro n hn
    have hn0 : N₀ ≤ n := (Finset.mem_Ico.mp hn).1
    obtain ⟨j, hjh, hjrep⟩ := htail n hn0
    refine ⟨(j : ℤ) * c, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨j, by simpa [s] using Nat.lt_succ_iff.mpr hjh, rfl⟩
    · exact hjrep
  obtain ⟨f₀, hf₀F, X, hX, hXcard⟩ :=
    exists_large_shift_piece hFne hcoverJ
  let u : ℤ := 2 * N₀ + (len : ℤ) - f₀
  have hXS : ∀ x ∈ X, x ∈ S := fun x hx => (hX x hx).1
  have hrefcover : ∀ x ∈ X, ∃ f ∈ F, u - x - f ∈ S := by
    intro x hx
    have hxJ := (hX x hx).2
    have hxupper : x + f₀ < N₀ + (len : ℤ) := (Finset.mem_Ico.mp hxJ).2
    have htailux : N₀ ≤ u - x := by
      dsimp [u]
      omega
    obtain ⟨j, hjh, hjrep⟩ := htail (u - x) htailux
    refine ⟨(j : ℤ) * c, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨j, by simpa [s] using Nat.lt_succ_iff.mpr hjh, rfl⟩
    · change ZRepExactly D h (u - x - (j : ℤ) * c)
      exact hjrep
  obtain ⟨f₁, hf₁F, C, hC, hCcard⟩ :=
    exists_large_reflected_piece hFne hXS hrefcover
  let v : ℤ := u - f₁
  have hJcard : J.card = len := by
    dsimp [J]
    rw [Int.card_Ico]
    simp
  have hFpos : 0 < F.card := Finset.card_pos.mpr hFne
  have hTcard : T ≤ (J.card / F.card) / F.card := by
    apply (Nat.le_div_iff_mul_le hFpos).2
    apply (Nat.le_div_iff_mul_le hFpos).2
    rw [hJcard]
    have hmul := Nat.mul_le_mul (Nat.mul_le_mul_left T hFcard) hFcard
    convert hmul using 1 <;> simp [len] <;> ring
  have hCbig : T ≤ C.card :=
    le_trans hTcard (le_trans (Nat.div_le_div_right hXcard) hCcard)
  let base : ℤ := N₀ - f₀
  let C' : Finset ℤ := C.image fun x => x - base
  have hC'card : C'.card = C.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    exact sub_left_injective hab
  let L : ℕ := len - 1
  have hC'bound : ∀ z ∈ C', 0 ≤ z ∧ z ≤ (L : ℤ) := by
    intro z hz
    obtain ⟨x, hxC, rfl⟩ := Finset.mem_image.mp hz
    have hxX := (hC x hxC).1
    have hxJ := (hX x hxX).2
    have hxlo := (Finset.mem_Ico.mp hxJ).1
    have hxhi := (Finset.mem_Ico.mp hxJ).2
    dsimp [base, L]
    have hlen_cast : ((len - 1 : ℕ) : ℤ) = (len : ℤ) - 1 := by omega
    rw [hlen_cast]
    constructor <;> omega
  let modulus : ℕ := R + 2 * L + 1
  have hmodpos : 0 < modulus := by simp [modulus]
  letI : NeZero modulus := ⟨Nat.ne_of_gt hmodpos⟩
  have hsize : (R : ℤ) + 2 * (L : ℤ) < (modulus : ℤ) := by
    dsimp [modulus]
    omega
  have hC'ne : C'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hz : C'.card = 0 := by simp [hempty]
    rw [hC'card] at hz
    have : T ≤ 0 := by simpa [hz] using hCbig
    omega
  have hRlen : R ≤ len := by
    have hsquare : 1 ≤ s ^ 2 := by
      have hm := Nat.mul_le_mul (show 1 ≤ s by omega) (show 1 ≤ s by omega)
      simpa [pow_two] using hm
    have hTlen : T ≤ len := by
      dsimp [len]
      have hm := Nat.mul_le_mul_right T hsquare
      simpa [mul_comm] using hm
    exact le_trans (by simp [T]) hTlen
  have hdense : modulus ≤ q * C'.card := by
    have hlenC : len ≤ s ^ 2 * C'.card := by
      dsimp [len]
      exact Nat.mul_le_mul_left (s ^ 2) (by simpa [hC'card] using hCbig)
    have hmod3 : modulus ≤ 3 * len := by
      dsimp [modulus, L]
      omega
    have h3len : 3 * len ≤ q * C'.card := by
      calc
        3 * len ≤ 3 * (s ^ 2 * C'.card) := Nat.mul_le_mul_left 3 hlenC
        _ ≤ (4 * s ^ 2) * C'.card := by ring_nf; omega
        _ = q * C'.card := by rfl
    exact le_trans hmod3 h3len
  have hqpos : 1 ≤ q := by
    dsimp [q]
    have : 1 ≤ s ^ 2 := by
      have hm := Nat.mul_le_mul (show 1 ≤ s by omega) (show 1 ≤ s by omega)
      simpa [pow_two] using hm
    omega
  obtain ⟨hΓcard, hΓlocal⟩ := local_integer_bogolyubov q hqpos
    hC'ne (by omega : (0 : ℤ) ≤ (L : ℤ)) (by omega : (0 : ℤ) ≤ (R : ℤ))
    hC'bound hsize hdense
  let A := integerResidues modulus C'
  let Γ := cyclicLargeSpectrum A ((A.card : ℝ) / (4 * q))
  have hdpos : 0 < d := by
    dsimp [d]
    positivity
  obtain ⟨e, he⟩ := exists_padded_enumeration Γ hdpos (by
    simpa [Γ, A] using hΓcard)
  let θ : Fin d → AddCircle (1 : ℝ) := fun j => ZMod.toAddCircle (e j)
  refine ⟨θ, 2 * v, ?_⟩
  intro x hxR hphase
  have hclose : ∀ k ∈ Γ,
      ‖ZMod.stdAddChar ((x : ZMod modulus) * k) - 1‖ ≤ (1 / 2 : ℝ) := by
    intro k hk
    obtain ⟨j, hj⟩ := he k hk
    have hp := hphase j
    dsimp [θ] at hp
    rw [hj, stdAddChar_int_zsmul_toAddCircle] at hp
    exact hp
  have hxabs : |x| ≤ (R : ℤ) := by
    calc
      |x| = (x.natAbs : ℤ) := (Int.natCast_natAbs x).symm
      _ ≤ (R : ℤ) := by exact_mod_cast hxR
  have hdiffC' : InFourfoldDifference (C' : Set ℤ) x := by
    apply hΓlocal x hxabs
    intro k hk
    exact hclose k (by simpa [Γ, A] using hk)
  have hdiffC : InFourfoldDifference (C : Set ℤ) x := by
    obtain ⟨a', ha', b', hb', c', hc', d', hd', heq⟩ := hdiffC'
    obtain ⟨a, haC, haeq⟩ := Finset.mem_image.mp ha'
    obtain ⟨b, hbC, hbeq⟩ := Finset.mem_image.mp hb'
    obtain ⟨cc, hcC, hceq⟩ := Finset.mem_image.mp hc'
    obtain ⟨dd, hdC, hdeq⟩ := Finset.mem_image.mp hd'
    refine ⟨a, by simpa using haC, b, by simpa using hbC,
      cc, by simpa using hcC, dd, by simpa using hdC, ?_⟩
    subst a'; subst b'; subst c'; subst d'
    linear_combination heq
  apply reflected_fourfoldDifference_rep
    (C := (C : Set ℤ)) (u := v)
  · intro a ha
    exact (hC a (by simpa using ha)).2.1
  · intro a ha
    exact (hC a (by simpa using ha)).2.2
  · exact hdiffC

end Erdos336
