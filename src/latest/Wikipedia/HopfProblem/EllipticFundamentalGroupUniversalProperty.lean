import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Iterate

/-!
# The universal property of cyclic affine normal forms

This file proves a group-presentation theorem from actual unique normal
forms. If every element has a unique expression `T(w) * h^r`, `0 ≤ r < m`,
the conjugation relation and the relation `h^m = T(v)` give the exact
universal property for the generators. It is a finite algebraic helper for
the geometric deck group; no assertion about a fundamental group is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CyclicNormalForms

variable {L G H : Type*} [AddCommGroup L] [Group G] [Group H]

/-- A translation followed by a nonnegative power of the affine generator. -/
def word (T : Multiplicative L →* G) (h : G) (w : L) (r : ℕ) : G :=
  T (Multiplicative.ofAdd w) * h ^ r

/-- The finite-exponent normal-form map. -/
def normalForm (T : Multiplicative L →* G) (h : G) (m : ℕ) (a : L × Fin m) : G :=
  word T h a.1 a.2.val

/-- Moving a translation through a power of the affine generator applies
the corresponding iterate of the lattice automorphism. -/
theorem pow_mul_translation
    (T : Multiplicative L →* G) (h : G) (A : L ≃+ L)
    (hconj : ∀ w, h * T (Multiplicative.ofAdd w) =
      T (Multiplicative.ofAdd (A w)) * h) (r : ℕ) (w : L) :
    h ^ r * T (Multiplicative.ofAdd w) =
      T (Multiplicative.ofAdd ((A : L → L)^[r] w)) * h ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    calc
      h ^ (r + 1) * T (Multiplicative.ofAdd w) =
          h * (h ^ r * T (Multiplicative.ofAdd w)) := by
            rw [pow_succ', mul_assoc]
      _ = h * (T (Multiplicative.ofAdd ((A : L → L)^[r] w)) * h ^ r) := by rw [ih]
      _ = (h * T (Multiplicative.ofAdd ((A : L → L)^[r] w))) * h ^ r :=
            (mul_assoc _ _ _).symm
      _ = (T (Multiplicative.ofAdd (A ((A : L → L)^[r] w))) * h) * h ^ r := by
            rw [hconj]
      _ = T (Multiplicative.ofAdd ((A : L → L)^[r + 1] w)) * h ^ (r + 1) := by
            rw [Function.iterate_succ_apply', pow_succ', mul_assoc]

theorem word_mul
    (T : Multiplicative L →* G) (h : G) (A : L ≃+ L)
    (hconj : ∀ w, h * T (Multiplicative.ofAdd w) =
      T (Multiplicative.ofAdd (A w)) * h)
    (w z : L) (r s : ℕ) :
    word T h w r * word T h z s = word T h (w + (A : L → L)^[r] z) (r + s) := by
  unfold word
  calc
    (T (Multiplicative.ofAdd w) * h ^ r) *
        (T (Multiplicative.ofAdd z) * h ^ s) =
      T (Multiplicative.ofAdd w) * ((h ^ r * T (Multiplicative.ofAdd z)) * h ^ s) := by
        simp only [mul_assoc]
    _ = T (Multiplicative.ofAdd w) *
        ((T (Multiplicative.ofAdd ((A : L → L)^[r] z)) * h ^ r) * h ^ s) := by
          rw [pow_mul_translation T h A hconj]
    _ = (T (Multiplicative.ofAdd w) *
        T (Multiplicative.ofAdd ((A : L → L)^[r] z))) * (h ^ r * h ^ s) := by
          simp only [mul_assoc]
    _ = T (Multiplicative.ofAdd (w + (A : L → L)^[r] z)) * h ^ (r + s) := by
          rw [ofAdd_add, map_mul, pow_add]

/-- Euclidean division of an exponent accounts for the translation carry. -/
theorem pow_reduce (T : Multiplicative L →* G) (h : G) {m : ℕ} {v : L}
    (hpow : h ^ m = T (Multiplicative.ofAdd v)) (n : ℕ) :
    h ^ n = T (Multiplicative.ofAdd ((n / m) • v)) * h ^ (n % m) := by
  calc
    h ^ n = h ^ (m * (n / m) + n % m) := by rw [Nat.div_add_mod]
    _ = (h ^ m) ^ (n / m) * h ^ (n % m) := by rw [pow_add, pow_mul]
    _ = T (Multiplicative.ofAdd ((n / m) • v)) * h ^ (n % m) := by
      rw [hpow, ofAdd_nsmul, map_pow]

theorem word_reduce (T : Multiplicative L →* G) (h : G) {m : ℕ} {v : L}
    (hpow : h ^ m = T (Multiplicative.ofAdd v)) (w : L) (n : ℕ) :
    word T h w n = word T h (w + (n / m) • v) (n % m) := by
  unfold word
  rw [pow_reduce T h hpow n, ofAdd_add, map_mul, mul_assoc]

/-- The unique normal coordinates of an element of the source group. -/
def normalFormEquiv (T : Multiplicative L →* G) (h : G) (m : ℕ)
    (hnf : Function.Bijective (normalForm T h m)) : (L × Fin m) ≃ G :=
  Equiv.ofBijective (normalForm T h m) hnf

/-- Evaluate a source element's unique normal form in a target group. -/
def extensionFunction (T : Multiplicative L →* G) (h : G) (m : ℕ)
    (hnf : Function.Bijective (normalForm T h m))
    (τ : Multiplicative L →* H) (k : H) : G → H :=
  normalForm τ k m ∘ (normalFormEquiv T h m hnf).symm

theorem extensionFunction_normalForm (T : Multiplicative L →* G) (h : G) (m : ℕ)
    (hnf : Function.Bijective (normalForm T h m))
    (τ : Multiplicative L →* H) (k : H) (a : L × Fin m) :
    extensionFunction T h m hnf τ k (normalForm T h m a) = normalForm τ k m a := by
  change normalForm τ k m ((normalFormEquiv T h m hnf).symm
    ((normalFormEquiv T h m hnf) a)) = _
  rw [Equiv.symm_apply_apply]

/-- The normal-form evaluation respects words of every exponent, including
the carries that occur when the exponent is not smaller than `m`. -/
theorem extensionFunction_word (T : Multiplicative L →* G) (h : G) (m : ℕ)
    (hm : 0 < m) (v : L) (hpow : h ^ m = T (Multiplicative.ofAdd v))
    (hnf : Function.Bijective (normalForm T h m))
    (τ : Multiplicative L →* H) (k : H) (hkpow : k ^ m = τ (Multiplicative.ofAdd v))
    (w : L) (n : ℕ) :
    extensionFunction T h m hnf τ k (word T h w n) = word τ k w n := by
  rw [word_reduce T h hpow w n]
  have hf := extensionFunction_normalForm T h m hnf τ k
    (w + (n / m) • v, ⟨n % m, Nat.mod_lt n hm⟩)
  exact hf.trans (word_reduce τ k hkpow w n).symm

/-- Exhaustion by the normal forms already gives uniqueness of a
homomorphism with prescribed values on the translations and generator. -/
theorem hom_ext (T : Multiplicative L →* G) (h : G) (m : ℕ)
    (hnf : Function.Surjective (normalForm T h m)) (f g : G →* H)
    (hT : ∀ w, f (T (Multiplicative.ofAdd w)) = g (T (Multiplicative.ofAdd w)))
    (hh : f h = g h) : f = g := by
  apply MonoidHom.ext
  intro x
  obtain ⟨a, rfl⟩ := hnf x
  simp only [normalForm, word, map_mul, map_pow, hT, hh]

theorem extensionFunction_mul
    (T : Multiplicative L →* G) (h : G) (m : ℕ) (hm : 0 < m) (A : L ≃+ L) (v : L)
    (hconj : ∀ w, h * T (Multiplicative.ofAdd w) =
      T (Multiplicative.ofAdd (A w)) * h)
    (hpow : h ^ m = T (Multiplicative.ofAdd v))
    (hnf : Function.Bijective (normalForm T h m))
    (τ : Multiplicative L →* H) (k : H)
    (hkconj : ∀ w, k * τ (Multiplicative.ofAdd w) =
      τ (Multiplicative.ofAdd (A w)) * k)
    (hkpow : k ^ m = τ (Multiplicative.ofAdd v)) (x y : G) :
    extensionFunction T h m hnf τ k (x * y) =
      extensionFunction T h m hnf τ k x * extensionFunction T h m hnf τ k y := by
  obtain ⟨a, rfl⟩ := hnf.surjective x
  obtain ⟨b, rfl⟩ := hnf.surjective y
  change extensionFunction T h m hnf τ k
    (word T h a.1 a.2.val * word T h b.1 b.2.val) =
      extensionFunction T h m hnf τ k (word T h a.1 a.2.val) *
        extensionFunction T h m hnf τ k (word T h b.1 b.2.val)
  rw [word_mul T h A hconj,
    extensionFunction_word T h m hm v hpow hnf τ k hkpow,
    extensionFunction_word T h m hm v hpow hnf τ k hkpow,
    extensionFunction_word T h m hm v hpow hnf τ k hkpow,
    word_mul τ k A hkconj]

/-- The homomorphism defined by evaluating the unique source normal forms
in target generators that satisfy the same two relations. -/
def extendHom
    (T : Multiplicative L →* G) (h : G) (m : ℕ) (hm : 0 < m) (A : L ≃+ L) (v : L)
    (hconj : ∀ w, h * T (Multiplicative.ofAdd w) =
      T (Multiplicative.ofAdd (A w)) * h)
    (hpow : h ^ m = T (Multiplicative.ofAdd v))
    (hnf : Function.Bijective (normalForm T h m))
    (τ : Multiplicative L →* H) (k : H)
    (hkconj : ∀ w, k * τ (Multiplicative.ofAdd w) =
      τ (Multiplicative.ofAdd (A w)) * k)
    (hkpow : k ^ m = τ (Multiplicative.ofAdd v)) : G →* H :=
  MonoidHom.mk' (extensionFunction T h m hnf τ k)
    (extensionFunction_mul T h m hm A v hconj hpow hnf τ k hkconj hkpow)

theorem extendHom_word
    (T : Multiplicative L →* G) (h : G) (m : ℕ) (hm : 0 < m) (A : L ≃+ L) (v : L)
    (hconj : ∀ w, h * T (Multiplicative.ofAdd w) =
      T (Multiplicative.ofAdd (A w)) * h)
    (hpow : h ^ m = T (Multiplicative.ofAdd v))
    (hnf : Function.Bijective (normalForm T h m))
    (τ : Multiplicative L →* H) (k : H)
    (hkconj : ∀ w, k * τ (Multiplicative.ofAdd w) =
      τ (Multiplicative.ofAdd (A w)) * k)
    (hkpow : k ^ m = τ (Multiplicative.ofAdd v)) (w : L) (n : ℕ) :
    extendHom T h m hm A v hconj hpow hnf τ k hkconj hkpow (word T h w n) =
      word τ k w n :=
  extensionFunction_word T h m hm v hpow hnf τ k hkpow w n

theorem extendHom_translation
    (T : Multiplicative L →* G) (h : G) (m : ℕ) (hm : 0 < m) (A : L ≃+ L) (v : L)
    (hconj : ∀ w, h * T (Multiplicative.ofAdd w) =
      T (Multiplicative.ofAdd (A w)) * h)
    (hpow : h ^ m = T (Multiplicative.ofAdd v))
    (hnf : Function.Bijective (normalForm T h m))
    (τ : Multiplicative L →* H) (k : H)
    (hkconj : ∀ w, k * τ (Multiplicative.ofAdd w) =
      τ (Multiplicative.ofAdd (A w)) * k)
    (hkpow : k ^ m = τ (Multiplicative.ofAdd v)) (w : L) :
    extendHom T h m hm A v hconj hpow hnf τ k hkconj hkpow
      (T (Multiplicative.ofAdd w)) = τ (Multiplicative.ofAdd w) := by
  simpa only [word, pow_zero, mul_one] using
    extendHom_word T h m hm A v hconj hpow hnf τ k hkconj hkpow w 0

theorem extendHom_generator
    (T : Multiplicative L →* G) (h : G) (m : ℕ) (hm : 0 < m) (A : L ≃+ L) (v : L)
    (hconj : ∀ w, h * T (Multiplicative.ofAdd w) =
      T (Multiplicative.ofAdd (A w)) * h)
    (hpow : h ^ m = T (Multiplicative.ofAdd v))
    (hnf : Function.Bijective (normalForm T h m))
    (τ : Multiplicative L →* H) (k : H)
    (hkconj : ∀ w, k * τ (Multiplicative.ofAdd w) =
      τ (Multiplicative.ofAdd (A w)) * k)
    (hkpow : k ^ m = τ (Multiplicative.ofAdd v)) :
    extendHom T h m hm A v hconj hpow hnf τ k hkconj hkpow h = k := by
  simpa only [word, ofAdd_zero, map_one, one_mul, pow_one] using
    extendHom_word T h m hm A v hconj hpow hnf τ k hkconj hkpow 0 1

/-- The exact universal property of the translation/conjugation/power
presentation. Unique normal forms are proved for the source group before
this theorem is applied; the target needs only the two stated relations. -/
theorem existsUnique_hom_of_normalForms
    (T : Multiplicative L →* G) (h : G) (m : ℕ) (hm : 0 < m) (A : L ≃+ L) (v : L)
    (hconj : ∀ w, h * T (Multiplicative.ofAdd w) =
      T (Multiplicative.ofAdd (A w)) * h)
    (hpow : h ^ m = T (Multiplicative.ofAdd v))
    (hnf : Function.Bijective (normalForm T h m))
    (τ : Multiplicative L →* H) (k : H)
    (hkconj : ∀ w, k * τ (Multiplicative.ofAdd w) =
      τ (Multiplicative.ofAdd (A w)) * k)
    (hkpow : k ^ m = τ (Multiplicative.ofAdd v)) :
    ∃! F : G →* H,
      (∀ w, F (T (Multiplicative.ofAdd w)) = τ (Multiplicative.ofAdd w)) ∧ F h = k := by
  let F := extendHom T h m hm A v hconj hpow hnf τ k hkconj hkpow
  have hFT : ∀ w, F (T (Multiplicative.ofAdd w)) = τ (Multiplicative.ofAdd w) :=
    extendHom_translation T h m hm A v hconj hpow hnf τ k hkconj hkpow
  have hFh : F h = k := extendHom_generator T h m hm A v hconj hpow hnf τ k hkconj hkpow
  refine ⟨F, ⟨hFT, hFh⟩, ?_⟩
  intro F' hF'
  exact hom_ext T h m hnf.surjective F' F
    (fun w => (hF'.1 w).trans (hFT w).symm) (hF'.2.trans hFh.symm)

end Wikipedia.HopfProblem.CyclicNormalForms
