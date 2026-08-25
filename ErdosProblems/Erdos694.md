This is a formalized proof of [Erdős Problem 694](https://www.erdosproblems.com/forum/thread/694).

The latest version is unconditional: `erdos_694` and
`totient_collision_construction` depend only on `propext`, `Classical.choice`,
and `Quot.sound`. The archived versions below retain the Linnik axiom.

### Unconditional lower bound

The replacement proof avoids Linnik's theorem. Fix a positive integer `D` and
put `Y = k^D`. The proved uniform prime-counting estimate supplies enough
primes in `(2^k, 2^(k+1)]`, congruent to one modulo each prime divisor of
`A = ∏_{p ≤ Y} (p - 1)`. Counting factors with multiplicity, `A` has at most
`2Y` prime factors. Choose distinct primes in that interval so that their
product `N` satisfies `A ∣ φ(N)`. The dyadic interval also ensures
`gcd(N, φ(N)) = 1`.

Set `P = ∏_{p ≤ Y} p`, `U = φ(N)/A`, and let `Q` be the product of the
prime divisors of `U` exceeding `Y`. Then `a = NQ` and `b = PUQ` satisfy
`φ(a) = φ(b)` and

```
b/a = (P/A) · φ(N)/N,
φ(a) ≤ N² ≤ exp(8 k^(D+1)),
φ(N)/N ≥ 1 - 2k^D/2^k.
```

Mertens' product theorem and inversion of the height bound give a lower-bound
coefficient `e^γ D/(D+1)` for every `D`. Letting `D` grow recovers `e^γ`.
The formal argument is in
[Unconditional.lean](../src/latest/ErdosProblems/Erdos694/Unconditional.lean)
and its supporting modules. The earlier prime-based height lemma remains
available with its prime-existence hypothesis explicit.

### Versions

It is available for these Mathlib (and Lean) versions:

* [Mathlib/Lean v4.33.0](../src/latest/ErdosProblems/Erdos694.lean) (latest stable release).
* [Mathlib/Lean v4.32.0](../src/v4.32.0/ErdosProblems/Erdos694.lean).
* [Mathlib/Lean v4.30.0](../src/v4.30.0/ErdosProblems/Erdos694.lean).
* [Mathlib/Lean v4.29.1](../src/v4.29.1/ErdosProblems/Erdos694.lean).
