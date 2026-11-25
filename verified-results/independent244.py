"""Exact positive-root counts for independent triples with staggered supports.

Each exponent 0..11 occurs in exactly one base. The coefficient at degree j
is +/- B^(121-j^2), so different terms dominate at different positive inputs.
The distinct nonempty supports guarantee linear independence.
"""

from itertools import product
from fractions import Fraction
from math import comb, lcm
from random import Random


def variations(seq):
    signs = [v > 0 for v in seq if v]
    return sum(a != b for a, b in zip(signs, signs[1:]))


def positive_count(coeff):
    # With t=x/(1+x), (1-t)^d P(t/(1-t)) has Bernstein coefficients
    # coeff[i]/binom(d,i). Clear their denominators with a positive scale.
    d = len(coeff) - 1
    scale = lcm(*(comb(d, i) for i in range(d + 1)))
    stack = [([v * (scale // comb(d, i)) for i, v in enumerate(coeff)], 0)]
    count = 0
    while stack:
        b, depth = stack.pop()
        v = variations(b)
        if v <= 1:
            count += v
            continue
        if depth >= 256:
            raise ArithmeticError("unresolved interval")
        # De Casteljau at 1/2. Each child has the common scale 2^d.
        left, right = [], []
        for k in range(d + 1):
            left.append(b[0] << (d-k))
            right.append(b[-1] << (d-k))
            b = [a + c for a, c in zip(b, b[1:])]
        count += int(left[-1] == 0)
        stack.extend(((left, depth + 1), (right[::-1], depth + 1)))
    return count


def expand(order, signs, base):
    coeff = [0] * 34
    terms = [s * base ** (121-j*j) for j, s in enumerate(signs)]
    for k in range(0, 12, 4):
        for i, j, h in product(order[k:k+4], repeat=3):
            coeff[i+j+h] += terms[i] * terms[j] * terms[h]
    return coeff


def main():
    assert positive_count([-2, 1]) == 1
    assert positive_count([2, -3, 1]) == 2
    assert positive_count([0, -1, 1]) == 1
    rng = Random(244)
    max_count = max_variations = 0
    for i in range(120):
        order = list(range(12))
        rng.shuffle(order)
        signs = [(-1)**j if i % 2 == 0 else rng.choice((-1, 1)) for j in range(12)]
        coeff = expand(order, signs, 2 + i % 3)
        v = variations(coeff)
        roots = positive_count(coeff)
        assert roots <= v and (v - roots) % 2 == 0
        max_count = max(max_count, roots)
        max_variations = max(max_variations, v)
    print(f"120 independent triples; maximum positive roots {max_count}; "
          f"maximum coefficient sign changes {max_variations}")
    order = [0, 5, 6, 11, 1, 2, 7, 8, 3, 4, 9, 10]
    signs = [(-1)**j for j in range(12)]
    # At each listed x the three bases have coefficients (-1)^j 4^(121-j^2).
    # Denominators are positive. By continuity, opposite signs at successive
    # endpoints give distinct positive roots inside disjoint open intervals.
    points = [2, Fraction(275, 64), Fraction(245, 4), Fraction(257, 4),
              Fraction(269, 4), 1024, 15680, 16448, 17216, 263168, 4014080,
              4210688, 4407296, 67108864, 1027604480, 1073741824, 1128267776,
              17246978048, 263066746880, 274877906944, 288836550656,
              4105988734976]
    assert all(0 < a < b for a, b in zip(points, points[1:]))
    for k, x in enumerate(points):
        p, q = x.numerator, x.denominator
        terms = [s * 4**(121-j*j) * p**j * q**(11-j) for j, s in enumerate(signs)]
        scaled_sum = sum(sum(terms[j] for j in order[i:i+4])**3 for i in (0, 4, 8))
        assert (-1)**k * scaled_sum > 0
    assert positive_count(expand(order, signs, 4)) == 21
    print("Explicit triple: 21 disjoint sign changes; exact positive-root count 21")


if __name__ == "__main__":
    main()
