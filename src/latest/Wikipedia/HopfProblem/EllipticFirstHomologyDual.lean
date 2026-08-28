import Wikipedia.HopfProblem.EllipticFirstHomologyAbelianization

/-!
# Integral characters of the actual elliptic abelianization

Restriction to the actual lattice translations is injective. Its image
consists precisely of the monodromy-invariant integral functionals whose
value on the twist is divisible by the elliptic order. Existence uses
the proved presentation of the actual deck group and the universal
property of its actual abelianization.

These are statements about integral group characters, without an assumed
identification with singular cohomology.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.Elliptic

/-- Restrict an integral character along the actual lattice translations
in the abelianization. -/
def deckAbelianRestriction (j : Kind) (v : Lattice) :
    (DeckAbelianization j v →+ ℤ) →ₗ[ℤ] (Lattice →ₗ[ℤ] ℤ) where
  toFun f := f.toIntLinearMap.comp (deckAbelianTranslation j v)
  map_add' f g := by apply LinearMap.ext; intro w; rfl
  map_smul' a f := by apply LinearMap.ext; intro w; rfl

@[simp] theorem deckAbelianRestriction_apply (j : Kind) (v : Lattice)
    (f : DeckAbelianization j v →+ ℤ) (w : Lattice) :
    deckAbelianRestriction j v f w = f (deckAbelianTranslation j v w) := rfl

theorem deckAbelianRestriction_monodromy (j : Kind) (v : Lattice)
    (f : DeckAbelianization j v →+ ℤ) (w : Lattice) :
    deckAbelianRestriction j v f (j.matrix *ᵥ w) = deckAbelianRestriction j v f w := by
  simp only [deckAbelianRestriction_apply, deckAbelianTranslation_monodromy]

/-- The affine power relation forces divisibility of the restricted
character's value on the twist. -/
theorem deckAbelianRestriction_dvd (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (f : DeckAbelianization j v →+ ℤ) :
    (j.order : ℤ) ∣ deckAbelianRestriction j v f v := by
  refine ⟨f (deckAbelianGenerator j v), ?_⟩
  have h := congrArg f (deckAbelianGenerator_order j v hv)
  simpa only [deckAbelianRestriction_apply, map_nsmul, nsmul_eq_mul] using h.symm

/-- Every normal form evaluates to its translation class plus its finite
exponent times the actual affine-generator class. -/
theorem deckAbelian_of_normalForm (j : Kind) (v : Lattice) (a : Lattice × Fin j.order) :
    Additive.ofMul (Abelianization.of (deckNormalForm j v a)) =
      deckAbelianTranslation j v a.1 + a.2.val • deckAbelianGenerator j v := by
  change Additive.ofMul (Abelianization.of
    (deckTranslationHom j v (Multiplicative.ofAdd a.1) * deckGenerator j v ^ a.2.val)) = _
  rw [map_mul, map_pow, ofMul_mul, ofMul_pow]
  rfl

/-- An integral character is determined by its restriction to the
translation lattice: the generator value is determined after multiplication
by the nonzero elliptic order. -/
theorem deckAbelianRestriction_injective (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) : Function.Injective (deckAbelianRestriction j v) := by
  intro f g hfg
  have ht (w : Lattice) : f (deckAbelianTranslation j v w) =
      g (deckAbelianTranslation j v w) := congrArg (fun ξ : Lattice →ₗ[ℤ] ℤ => ξ w) hfg
  have hm : (j.order : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt j.order_pos)
  have hf : (j.order : ℤ) * f (deckAbelianGenerator j v) =
      f (deckAbelianTranslation j v v) := by
    simpa only [map_nsmul, nsmul_eq_mul] using congrArg f (deckAbelianGenerator_order j v hv.1)
  have hg : (j.order : ℤ) * g (deckAbelianGenerator j v) =
      g (deckAbelianTranslation j v v) := by
    simpa only [map_nsmul, nsmul_eq_mul] using congrArg g (deckAbelianGenerator_order j v hv.1)
  have hgen : f (deckAbelianGenerator j v) = g (deckAbelianGenerator j v) :=
    mul_left_cancel₀ hm (hf.trans ((ht v).trans hg.symm))
  apply AddMonoidHom.ext
  intro x
  obtain ⟨k, hk⟩ := Quotient.exists_rep x.toMul
  have hx : Additive.ofMul (Abelianization.of k) = x := congrArg Additive.ofMul hk
  rw [← hx]
  obtain ⟨a, rfl⟩ := deckNormalForm_surjective j v hv.1 k
  rw [deckAbelian_of_normalForm, map_add, map_add, map_nsmul, map_nsmul, ht, hgen]

/-- Construct an extension through the genuine group presentation and
the genuine abelianization. -/
theorem exists_deckAbelian_extension (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (ξ : Lattice →ₗ[ℤ] ℤ)
    (hξ : ∀ w, ξ (j.matrix *ᵥ w) = ξ w) (hdiv : (j.order : ℤ) ∣ ξ v) :
    ∃ f : DeckAbelianization j v →+ ℤ, deckAbelianRestriction j v f = ξ := by
  obtain ⟨k, hk⟩ := hdiv
  let τ : Multiplicative Lattice →* Multiplicative ℤ := ξ.toAddMonoidHom.toMultiplicative
  have hc : ∀ w, Multiplicative.ofAdd k * τ (Multiplicative.ofAdd w) =
      τ (Multiplicative.ofAdd (j.matrix *ᵥ w)) * Multiplicative.ofAdd k := by
    intro w
    change Multiplicative.ofAdd (k + ξ w) = Multiplicative.ofAdd (ξ (j.matrix *ᵥ w) + k)
    rw [hξ, add_comm]
  have hp : Multiplicative.ofAdd k ^ j.order = τ (Multiplicative.ofAdd v) := by
    apply Multiplicative.toAdd.injective
    change j.order • k = ξ v
    simpa only [nsmul_eq_mul] using hk.symm
  obtain ⟨F, hF, _⟩ := affineDeckGroup_presentation j v hv τ (Multiplicative.ofAdd k) hc hp
  refine ⟨(Abelianization.lift F).toAdditiveLeft, ?_⟩
  apply LinearMap.ext
  intro w
  exact congrArg Multiplicative.toAdd (hF.1 w)

/-- Exact extension criterion for an integral lattice functional. -/
theorem deckAbelianRestriction_extend_iff (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (ξ : Lattice →ₗ[ℤ] ℤ) :
    (∃ f : DeckAbelianization j v →+ ℤ, deckAbelianRestriction j v f = ξ) ↔
      (∀ w, ξ (j.matrix *ᵥ w) = ξ w) ∧ (j.order : ℤ) ∣ ξ v := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨deckAbelianRestriction_monodromy j v f, deckAbelianRestriction_dvd j v hv.1 f⟩
  · rintro ⟨hξ, hdiv⟩
    exact exists_deckAbelian_extension j v hv ξ hξ hdiv

theorem deckAbelianRestriction_range (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (ξ : Lattice →ₗ[ℤ] ℤ) :
    ξ ∈ LinearMap.range (deckAbelianRestriction j v) ↔
      (∀ w, ξ (j.matrix *ᵥ w) = ξ w) ∧ (j.order : ℤ) ∣ ξ v :=
  deckAbelianRestriction_extend_iff j v hv ξ

/-- Every functional satisfying the extension criterion has exactly one
extension to an integral character of the actual abelianization. -/
theorem existsUnique_deckAbelian_extension (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (ξ : Lattice →ₗ[ℤ] ℤ)
    (hξ : ∀ w, ξ (j.matrix *ᵥ w) = ξ w) (hdiv : (j.order : ℤ) ∣ ξ v) :
    ∃! f : DeckAbelianization j v →+ ℤ, deckAbelianRestriction j v f = ξ := by
  obtain ⟨f, hf⟩ := exists_deckAbelian_extension j v hv ξ hξ hdiv
  refine ⟨f, hf, ?_⟩
  intro g hg
  exact deckAbelianRestriction_injective j v hv (hg.trans hf.symm)


/-- The integral functional with coefficients in the invariant basis `(γ, ψⱼ)`. -/
def coinvariantFunctional (j : Kind) (c : Fin 2 → ℤ) : Lattice →ₗ[ℤ] ℤ where
  toFun w := c 0 * γ w + c 1 * psi j w
  map_add' w z := by
    simp only [γ, Pi.add_apply, map_add]
    ring
  map_smul' a w := by
    simp only [γ, Pi.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem coinvariantFunctional_apply (j : Kind) (c : Fin 2 → ℤ)
    (w : Lattice) :
    coinvariantFunctional j c w = c 0 * γ w + c 1 * psi j w := rfl

/-- Evaluation on the explicit coinvariant section is the ordinary dot product. -/
@[simp] theorem coinvariantFunctional_section (j : Kind) (c z : Fin 2 → ℤ) :
    coinvariantFunctional j c (coinvariantSection j z) = c 0 * z 0 + c 1 * z 1 := by
  have h0 := congrFun (coinvariantMap_section j z) 0
  have h1 := congrFun (coinvariantMap_section j z) 1
  change γ (coinvariantSection j z) = z 0 at h0
  change psi j (coinvariantSection j z) = z 1 at h1
  simp only [coinvariantFunctional_apply, h0, h1]

/-- All coefficient functionals are invariant under the actual integral monodromy. -/
theorem coinvariantFunctional_monodromy (j : Kind) (c : Fin 2 → ℤ) (w : Lattice) :
    coinvariantFunctional j c (j.matrix *ᵥ w) = coinvariantFunctional j c w := by
  have h0 := congrFun (coinvariantMap_monodromy j w) 0
  have h1 := congrFun (coinvariantMap_monodromy j w) 1
  change γ (j.matrix *ᵥ w) = γ w at h0
  change psi j (j.matrix *ᵥ w) = psi j w at h1
  simp only [coinvariantFunctional_apply, h0, h1]

/-- The invariant coefficients are unique over the integers. -/
theorem coinvariantFunctional_injective (j : Kind) :
    Function.Injective (coinvariantFunctional j) := by
  intro c d h
  have h0 := congrArg (fun f : Lattice →ₗ[ℤ] ℤ => f (coinvariantSection j ![1, 0])) h
  have h1 := congrArg (fun f : Lattice →ₗ[ℤ] ℤ => f (coinvariantSection j ![0, 1])) h
  simp only [coinvariantFunctional_section, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, mul_one, mul_zero, add_zero, zero_add] at h0 h1
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- The two values on section basis vectors are the invariant coefficients. -/
def coinvariantFunctionalCoefficients (j : Kind) (ξ : Lattice →ₗ[ℤ] ℤ) : Fin 2 → ℤ :=
  ![ξ (coinvariantSection j ![1, 0]), ξ (coinvariantSection j ![0, 1])]

@[simp] theorem coinvariantFunctionalCoefficients_functional (j : Kind) (c : Fin 2 → ℤ) :
    coinvariantFunctionalCoefficients j (coinvariantFunctional j c) = c := by
  ext i
  fin_cases i
  · change coinvariantFunctional j c (coinvariantSection j ![1, 0]) = c 0
    rw [coinvariantFunctional_section]
    simp
  · change coinvariantFunctional j c (coinvariantSection j ![0, 1]) = c 1
    rw [coinvariantFunctional_section]
    simp

/-- Linear functionals on the section split into the two integral coordinates. -/
theorem map_coinvariantSection (j : Kind) (ξ : Lattice →ₗ[ℤ] ℤ) (z : Fin 2 → ℤ) :
    ξ (coinvariantSection j z) =
      z 0 * ξ (coinvariantSection j ![1, 0]) +
        z 1 * ξ (coinvariantSection j ![0, 1]) := by
  have hz : z = z 0 • ![1, 0] + z 1 • ![0, 1] := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hz]
  simp only [map_add, map_smul, smul_eq_mul]

/-- Every invariant integral functional equals its explicit coefficient functional. -/
theorem invariant_eq_coinvariantFunctional (j : Kind) (ξ : Lattice →ₗ[ℤ] ℤ)
    (hξ : ∀ w, ξ (j.matrix *ᵥ w) = ξ w) :
    ξ = coinvariantFunctional j (coinvariantFunctionalCoefficients j ξ) := by
  apply LinearMap.ext
  intro w
  calc
    ξ w = ξ (coinvariantSection j (coinvariantMap j w)) :=
      (invariant_map_section_coinvariantMap j ξ.toAddMonoidHom hξ w).symm
    _ = coinvariantFunctional j (coinvariantFunctionalCoefficients j ξ) w := by
      rw [map_coinvariantSection]
      simp only [coinvariantMap_zero_coordinate, coinvariantMap_one_coordinate,
        coinvariantFunctional_apply, coinvariantFunctionalCoefficients,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      ring

/-- The integral dual of the coinvariants is exactly the invariant dual lattice. -/
theorem invariant_iff_exists_coinvariantFunctional (j : Kind) (ξ : Lattice →ₗ[ℤ] ℤ) :
    (∀ w, ξ (j.matrix *ᵥ w) = ξ w) ↔
      ∃ c : Fin 2 → ℤ, ξ = coinvariantFunctional j c := by
  constructor
  · intro hξ
    exact ⟨coinvariantFunctionalCoefficients j ξ, invariant_eq_coinvariantFunctional j ξ hξ⟩
  · rintro ⟨c, rfl⟩
    exact coinvariantFunctional_monodromy j c

/-- The main twists have zero second coinvariant coordinate. -/
@[simp] theorem psi_twist (j : Kind) : psi j j.twist = 0 := by
  cases j <;> decide

/-- The twist evaluates to the signed first invariant coefficient. -/
theorem coinvariantFunctional_twist (j : Kind) (c : Fin 2 → ℤ) :
    coinvariantFunctional j c j.twist = (if j = .three then 1 else -1) * c 0 := by
  simp [Kind.twist_gamma, mul_comm]

/-- Integral extendibility on the main twist is precisely divisibility of the first coefficient. -/
theorem order_dvd_coinvariantFunctional_twist_iff (j : Kind) (c : Fin 2 → ℤ) :
    (j.order : ℤ) ∣ coinvariantFunctional j c j.twist ↔ (j.order : ℤ) ∣ c 0 := by
  rw [coinvariantFunctional_twist]
  cases j <;> simp

/-- For the main twists, the allowed invariant dual lattice has basis `(mγ, ψⱼ)`. -/
theorem invariant_and_order_dvd_twist_iff (j : Kind) (ξ : Lattice →ₗ[ℤ] ℤ) :
    ((∀ w, ξ (j.matrix *ᵥ w) = ξ w) ∧ (j.order : ℤ) ∣ ξ j.twist) ↔
      ∃ x y : ℤ, ξ = coinvariantFunctional j ![(j.order : ℤ) * x, y] := by
  constructor
  · rintro ⟨hξ, hdvd⟩
    obtain ⟨c, rfl⟩ := (invariant_iff_exists_coinvariantFunctional j ξ).mp hξ
    obtain ⟨x, hx⟩ := (order_dvd_coinvariantFunctional_twist_iff j c).mp hdvd
    refine ⟨x, c 1, ?_⟩
    congr 1
    ext i
    fin_cases i
    · simpa using hx
    · rfl
  · rintro ⟨x, y, rfl⟩
    refine ⟨coinvariantFunctional_monodromy j _, ?_⟩
    rw [order_dvd_coinvariantFunctional_twist_iff]
    exact ⟨x, rfl⟩

/-- The parameterized allowed functionals are integral combinations of `(mγ, ψⱼ)`. -/
theorem coinvariantFunctional_order_coefficients (j : Kind) (x y : ℤ) :
    coinvariantFunctional j ![(j.order : ℤ) * x, y] =
      x • ((j.order : ℤ) • (LinearMap.proj 0 : Lattice →ₗ[ℤ] ℤ)) + y • psi j := by
  apply LinearMap.ext
  intro w
  simp [coinvariantFunctional, γ]
  ring

/-- The divisibility condition defines exactly the integral span from Theorem 5.4(iii). -/
theorem invariant_and_order_dvd_twist_iff_mem_span (j : Kind) (ξ : Lattice →ₗ[ℤ] ℤ) :
    ((∀ w, ξ (j.matrix *ᵥ w) = ξ w) ∧ (j.order : ℤ) ∣ ξ j.twist) ↔
      ξ ∈ Submodule.span ℤ
        {((j.order : ℤ) • (LinearMap.proj 0 : Lattice →ₗ[ℤ] ℤ)), psi j} := by
  rw [invariant_and_order_dvd_twist_iff, Submodule.mem_span_pair]
  constructor
  · rintro ⟨x, y, rfl⟩
    exact ⟨x, y, (coinvariantFunctional_order_coefficients j x y).symm⟩
  · rintro ⟨x, y, hxy⟩
    refine ⟨x, y, ?_⟩
    rw [coinvariantFunctional_order_coefficients]
    exact hxy.symm

/-- In the invariant basis, the exact image condition is the source's
divisibility relation `m ∣ γ(v) x + ψⱼ(v) y`. -/
theorem deckAbelianRestriction_range_coefficients (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (ξ : Lattice →ₗ[ℤ] ℤ) :
    ξ ∈ LinearMap.range (deckAbelianRestriction j v) ↔
      ∃ c : Fin 2 → ℤ, ξ = coinvariantFunctional j c ∧
        (j.order : ℤ) ∣ γ v * c 0 + psi j v * c 1 := by
  rw [deckAbelianRestriction_range j v hv ξ]
  constructor
  · rintro ⟨hξ, hdiv⟩
    obtain ⟨c, rfl⟩ := (invariant_iff_exists_coinvariantFunctional j ξ).mp hξ
    refine ⟨c, rfl, ?_⟩
    simpa only [coinvariantFunctional_apply, mul_comm] using hdiv
  · rintro ⟨c, rfl, hdiv⟩
    refine ⟨coinvariantFunctional_monodromy j c, ?_⟩
    simpa only [coinvariantFunctional_apply, mul_comm] using hdiv

/-- For each of the source's main twists, the image of the actual dual
restriction is precisely the integral span of `mγ` and `ψⱼ`. -/
theorem mainDeckAbelianRestriction_range (j : Kind) :
    LinearMap.range (deckAbelianRestriction j j.twist) =
      Submodule.span ℤ
        {((j.order : ℤ) • (LinearMap.proj 0 : Lattice →ₗ[ℤ] ℤ)), psi j} := by
  ext ξ
  exact (deckAbelianRestriction_range j j.twist (mainTwist_admissible j) ξ).trans
    (invariant_and_order_dvd_twist_iff_mem_span j ξ)

/-- The first main image is `⟨3γ, ψ₁⟩`. -/
theorem threeDeckAbelianRestriction_range :
    LinearMap.range (deckAbelianRestriction .three ε) =
      Submodule.span ℤ {(3 : ℤ) • (LinearMap.proj 0 : Lattice →ₗ[ℤ] ℤ), psiOne} :=
  mainDeckAbelianRestriction_range .three

/-- The second main image is `⟨4γ, ψ₂⟩`, for the chosen twist `-ε'`. -/
theorem fourDeckAbelianRestriction_range :
    LinearMap.range (deckAbelianRestriction .four (-ε')) =
      Submodule.span ℤ {(4 : ℤ) • (LinearMap.proj 0 : Lattice →ₗ[ℤ] ℤ), psiTwo} :=
  mainDeckAbelianRestriction_range .four

end Wikipedia.HopfProblem.Elliptic
