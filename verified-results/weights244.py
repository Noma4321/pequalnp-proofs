"""Search all third-cube weights for sign changes on a fixed rational grid."""

from fractions import Fraction
from itertools import groupby


def samples():
    return sorted({Fraction(4**(2*j+1) * k, 128)
                   for j in range(11) for k in range(64, 257)})


def sweep(rows, weight):
    # For a fixed x, evaluate A^3 + weight*B^3 + t*C^3 up to a positive scale.
    # The sign changes at one rational threshold in t, or is constant.
    signs, critical = [], []
    for a, b, c in rows:
        constant = a + weight*b
        if not c and not constant:
            continue  # zero for every t at this sample
        i = len(signs)
        signs.append((-1 if c > 0 else 1) if c else (1 if constant > 0 else -1))
        if c:
            critical.append((-Fraction(constant, c), i))
    changes = sum(a != b for a, b in zip(signs, signs[1:]))
    best = changes
    for _, group in groupby(sorted(critical), key=lambda event: event[0]):
        # Only the two incident intervals change for each flipped sample.
        for _, i in group:
            for j in (i-1, i+1):
                if 0 <= j < len(signs):
                    changes += 1 if signs[i] == signs[j] else -1
            signs[i] *= -1
        best = max(best, changes)
    # At an exact threshold, omitting zero signs cannot increase the count
    # beyond that of either adjacent open interval.
    return best


def main():
    blocks = ((0, 5, 6, 11), (1, 2, 7, 8), (3, 4, 9, 10))
    grid = samples()
    rows = []
    for x in grid:
        p, q = x.numerator, x.denominator
        terms = [(-1)**j * 4**(121-j*j) * p**j * q**(11-j) for j in range(12)]
        rows.append(tuple(sum(terms[i] for i in block)**3 for block in blocks))
    weights = sorted({sgn * Fraction(2)**k for sgn in (-1, 1) for k in range(-24, 25)} | {0})
    maxima = [sweep(rows, w) for w in weights]
    print(f"{len(grid)} positive rational samples, {len(weights)} second-cube weights, "
          f"all real third-cube weights; largest sampled sign-change count {max(maxima)}")


if __name__ == "__main__":
    main()
