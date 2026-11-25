"""Exact seven-gate minimum for L-meta-13890. Run alongside search12598.py."""

from search12598 import INPUTS, check


TARGET = (3939035840 << 32) + 3939019264


def witness(a, b, c, d, e, f):
    be = b & e
    left = a & (d | be)
    bc = b & c
    right = bc & (e | f)
    return left | right


if __name__ == "__main__":
    if witness(*INPUTS) != TARGET:
        raise AssertionError("seven-gate circuit disagrees with a table row")
    if check(TARGET, 6) or not check(TARGET, 7):
        raise AssertionError("unexpected free-inversion synthesis result")
    print("Checked all 64 rows. Minimum seven even with free inversions; seven monotone gates suffice.")
