"""Five cubed binomials in L-gct-252, with exact integer coefficients."""

from fractions import Fraction

from independent244 import positive_bounds


def matchings(indices):
    if not indices:
        yield ()
        return
    a, *tail = indices
    for b in tail:
        for rest in matchings([c for c in tail if c != b]):
            yield ((a, b),) + rest


def polynomial(pairs, base):
    # The signed monomials are (-1)^j B^(81-j²) x^j, 0 <= j <= 9.
    # Each is used exactly once, in its assigned binomial.
    terms = [(-1)**j * base**(81-j*j) for j in range(10)]
    coeff = [0] * 28
    for a, b in pairs:
        for k, m in enumerate((1, 3, 3, 1)):
            coeff[(3-k)*a+k*b] += m * terms[a]**(3-k) * terms[b]**k
    return coeff


def main():
    tight = ((0, 9), (1, 2), (3, 4), (5, 6), (7, 8))
    example = polynomial(tight, 4)
    # Around an odd-indexed crossover three nearby samples separate the
    # three close roots. Multiply by the positive denominator to power 27.
    grid = sorted({Fraction(4**(2*j+1) * k, 128)
                   for j in range(9) for k in range(64, 257)})
    alternating = []
    for x in grid:
        value = sum(c * x.numerator**i * x.denominator**(27-i)
                    for i, c in enumerate(example))
        if value and (not alternating or alternating[-1][1] != (value > 0)):
            alternating.append((x, value > 0))
    if len(alternating) != 18 or positive_bounds(example) != (17, 17):
        raise AssertionError("failed the 17-root certificate")
    print("Endpoints of 17 disjoint sign-change intervals:", [str(x) for x, _ in alternating])
    histogram = {}
    for pairs in matchings(list(range(10))):
        coeff = polynomial(pairs, 4)
        # When all pairs have index sum nine, all five binomials vanish
        # at the same positive integer. Remove its full multiplicity and
        # count it once. The remainder of synthetic division is exact.
        shared = all(a + b == 9 for a, b in pairs)
        if shared:
            multiplicity = 0
            while len(coeff) > 1:
                q = [coeff[-1]]
                for c in reversed(coeff[1:-1]):
                    q.append(c + 4**9 * q[-1])
                if coeff[0] + 4**9 * q[-1]:
                    break
                coeff = q[::-1]
                multiplicity += 1
            if multiplicity < 3:
                raise AssertionError("missing common root")
        low, high = positive_bounds(coeff)
        if low != high:
            raise AssertionError("inconclusive root isolation")
        roots = low + int(shared)
        histogram[roots] = histogram.get(roots, 0) + 1
    print("distinct positive roots and matching counts:", sorted(histogram.items()))
    if sum(histogram.values()) != 945 or max(histogram) != 17:
        raise AssertionError("unexpected matching census")


if __name__ == "__main__":
    main()
