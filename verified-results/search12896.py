"""Run alongside search12598.py with Python 3. Inputs are numbered from zero."""

from search12598 import INPUTS, check


TARGET = (4276808392 << 32) + 4240490688


def witness(a, b, c, d, e, f):
    bc = b & c
    de = d & e
    either = b | c
    middle = de & either
    left = bc | middle
    af = a & f
    dor = d | e
    any_bde = b | dor
    right = af & any_bde
    return left | right


if __name__ == "__main__":
    if witness(*INPUTS) != TARGET:
        raise AssertionError("monotone circuit disagrees with target")
    print("The ten-gate monotone circuit matches all 64 rows.", flush=True)
    if check(TARGET, 8):
        raise AssertionError("found a circuit with eight binary gates and free inversions")
    print("No circuit with eight or fewer binary gates computes the table, even with free inversions.")
    print("Every circuit of size at most nine computing the table therefore uses only AND and OR.")
