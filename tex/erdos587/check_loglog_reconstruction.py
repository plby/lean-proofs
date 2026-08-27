#!/usr/bin/env python3
"""Finite regression checks for LOGLOG_RECONSTRUCTION.md, not a proof.

Uses exact rationals for divisor encodings and lattice lifting. The Gauss
identities and Gaussian major-arc samples use floating-point arithmetic.
Run: python3 tex/erdos587/check_loglog_reconstruction.py
"""

import cmath
from fractions import Fraction as F
import json
import math
import random


def nearest(x):
    return (x + F(1, 2)).__floor__()


def phase(x):
    return cmath.exp(2j * math.pi * float(x % 1))


def approximation(alpha, length):
    for b in range(1, length + 1):
        h = nearest(b * alpha)
        if math.gcd(h, b) == 1 and abs(alpha - F(h, b)) <= F(1, b * length):
            return h, b
    raise AssertionError((alpha, length))


def check_encodings():
    centered = reciprocal = 0
    for q in range(2, 70):
        for a in (1, 2, 5, 17):
            if math.gcd(a, q) != 1:
                continue
            for length in (2, 3, 5, 8, 13):
                for m in range(1, 35):
                    if q // math.gcd(m, q) <= length:
                        continue
                    alpha = F(a * m, q)
                    h, b = approximation(alpha, length)
                    beta = alpha - F(h, b)
                    t = a * m * b - q * h
                    assert t != 0
                    assert F(t, q * b) == beta
                    assert (m * b - pow(a, -1, q) * t) % q == 0
                    assert math.gcd(m * b, q) == math.gcd(t, q)
                    centered += 1

    for length in (2, 3, 5, 8, 13):
        for q in range(16 * length + 1, 16 * length + 22):
            for a, c in ((1, 1), (1, 4), (4, 8)):
                for r in range(1, 40):
                    if math.gcd(q, c * r) != 1:
                        continue
                    for v in (1, 2, 5, 11):
                        if math.gcd(q, v) != 1:
                            continue
                        numerator = a * v * pow(q, -1, c * r) % (c * r)
                        alpha = F(numerator, c * r)
                        h, b = approximation(alpha, length)
                        beta = alpha - F(h, b)
                        t = b * numerator - h * c * r
                        encoded = b * a * v - q * t
                        assert encoded != 0 and encoded % (c * r) == 0
                        assert F(t, b * c * r) == beta
                        assert math.gcd(b * a * v, q) == math.gcd(a * b, q)
                        reciprocal += 1
    return {"centered": centered, "reciprocal": reciprocal}


def gauss(a, ell, q):
    return sum(phase(F(a * s * s + ell * s, q)) for s in range(q))


def check_reciprocity():
    checked = 0
    maximum_error = 0.0
    for q in range(1, 65):
        for r in range(1, 21):
            if math.gcd(r, q) != 1:
                continue
            for v in (1, 2, 5, 11):
                if math.gcd(v, q) != 1:
                    continue
                b = -pow(v, -1, q) % q
                ratios = []
                for ell in range(-7, 8):
                    value = gauss(r * b, ell, q)
                    if q % 4 == 0:
                        if ell % 2:
                            assert abs(value) < 1e-8
                            continue
                        j = ell // 2
                        lhs = value * phase(F(-v * j * j, r * q))
                        rhs_phase = phase(F(-v * pow(q, -1, r) * j * j, r))
                    elif q % 2 == 0:
                        if ell % 2 == 0:
                            assert abs(value) < 1e-8
                            continue
                        q0 = q // 2
                        lhs = value * phase(F(-v * ell * ell, 8 * r * q0))
                        rhs_phase = phase(F(-v * pow(q0, -1, 8 * r) * ell * ell, 8 * r))
                    else:
                        lhs = value * phase(F(-v * ell * ell, 4 * r * q))
                        rhs_phase = phase(F(-v * pow(q, -1, 4 * r) * ell * ell, 4 * r))
                    ratios.append(lhs / rhs_phase)
                    checked += 1
                for value in ratios:
                    error = abs(value - ratios[0])
                    maximum_error = max(maximum_error, error)
                    assert error < 1e-8, (q, r, v, error)
                    assert abs(value) <= math.sqrt(2 * q) + 1e-8
    return {"identities": checked, "maximum_absolute_error": maximum_error}


def bezout(a, b):
    old_r, r, old_s, s, old_t, t = a, b, 1, 0, 0, 1
    while r:
        quotient = old_r // r
        old_r, r = r, old_r - quotient * r
        old_s, s = s, old_s - quotient * s
        old_t, t = t, old_t - quotient * t
    if old_r < 0:
        old_r, old_s, old_t = -old_r, -old_s, -old_t
    assert old_r == 1 and a * old_s + b * old_t == 1
    return old_s, old_t


def check_lifting():
    rng = random.Random(587)
    checked = 0
    eta = F(1, 8)
    for _ in range(400):
        v = (rng.randint(-10, 10), rng.randint(-10, 10))
        if math.gcd(*v) != 1:
            continue
        radii = (rng.randint(200, 400), rng.randint(200, 400))
        assert sum(F(v[i] ** 2, radii[i] ** 2) for i in range(2)) <= eta ** 2
        ell = (-v[1], v[0])
        lift = bezout(*ell)
        support_squared = sum((ell[i] * radii[i]) ** 2 for i in range(2))
        bound = math.isqrt(support_squared) * 7 // 8
        for _ in range(30):
            y = rng.randint(-bound, bound)
            assert y * y <= (1 - eta) ** 2 * support_squared
            real_lift = tuple(F(radii[i] ** 2 * ell[i] * y, support_squared) for i in range(2))
            integer_lift = tuple(y * lift[i] for i in range(2))
            axis = 0 if v[0] else 1
            along = (integer_lift[axis] - real_lift[axis]) / v[axis]
            assert all(integer_lift[i] - real_lift[i] == along * v[i] for i in range(2))
            rounded = tuple(integer_lift[i] - nearest(along) * v[i] for i in range(2))
            assert sum(ell[i] * rounded[i] for i in range(2)) == y
            assert sum(F(rounded[i] ** 2, radii[i] ** 2) for i in range(2)) <= 1
            checked += 1
    return {"exact_rational_lifts": checked}


def check_gaussian_major_arcs():
    rng = random.Random(587)
    maximum = (0.0, None)
    for _ in range(1500):
        length = rng.choice((2, 4, 8, 16, 32, 64, 128))
        b = rng.randint(1, length)
        h = rng.choice([h for h in range(b) if math.gcd(h, b) == 1])
        beta = rng.choice((0.0, 1 / length ** 2, 1 / (b * length), rng.random() / (b * length)))
        beta *= rng.choice((-1, 1))
        theta = rng.choice((0.0, rng.random(), rng.randrange(b) / b))
        alpha = h / b + beta
        value = sum(
            math.exp(-math.pi * (j / length) ** 2) * cmath.exp(2j * math.pi * ((alpha * j * j + theta * j) % 1))
            for j in range(-8 * length, 8 * length + 1)
        )
        ratio = abs(value) ** 2 * b * (1 + length * length * abs(beta)) / length ** 2
        if ratio > maximum[0]:
            maximum = (ratio, {"K": length, "b": b, "h": h, "beta": beta, "theta": theta})
        # A regression guard on these samples, NOT a universal bound.
        assert math.isfinite(ratio) and ratio < 32
    return {"samples": 1500, "maximum_normalized_value": maximum[0], "at": maximum[1]}


def check_exponents():
    epsilon, delta = F(1, 1000), F(1, 100)
    margins = {
        "reciprocal_modulus_separation": F(1, 16) - epsilon - delta,
        "reciprocal_average_separation": F(1, 4) - epsilon - 4 * F(1, 100),
        "noncritical_main_over_error": 5 - F(19, 8) - 1,
        "critical_main_over_error": 9 - F(27, 8),
        "small_step_power": F(1, 8) - 4 * epsilon,
        "structural_minimum_width": F(3 * 16, 4) - 11,
        "structural_area": F(9 * 16, 4) - 11,
    }
    assert all(value > 0 for value in margins.values())
    return {key: str(value) for key, value in margins.items()}


if __name__ == "__main__":
    print(json.dumps({
        "warning": "Finite regression tests only; these do not prove the new analytic or structural theorems.",
        "encodings": check_encodings(),
        "gauss_reciprocity": check_reciprocity(),
        "lattice_lifting": check_lifting(),
        "gaussian_major_arcs": check_gaussian_major_arcs(),
        "exponent_margins": check_exponents(),
    }, indent=2))
