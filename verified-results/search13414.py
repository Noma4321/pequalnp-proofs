"""Reproduce the L-meta-13414 optimum; run alongside search12598.py."""

from search12598 import check, monotone_witness


if __name__ == "__main__":
    target = (3939035336 << 32) + 3939035328
    circuit = monotone_witness(target, 8)
    if circuit is None or len(circuit) != 8 or check(target, 7):
        raise AssertionError("eight-gate minimum failed verification")
    print("Minimum eight, even with free inversions. Monotone witness checked on every row:")
    for output, (op, left, right) in enumerate(circuit, 6):
        print(f"{output} = {left} {op} {right}")
