"""Verify a critical-coordinate Taylor grid for the rational number field.

Requires python-flint 0.9.0. Run python rational_grid.py from any directory.
Every pass condition compares rigorous Arb enclosures or exact integers.
"""
import json
from fractions import Fraction

import flint
from flint import acb, arb, arb_series, ctx


def coefficients(length, precision):
    # The classical identity (s-1) zeta(s) = 1 + (s-1) zeta_deflated(s)
    # removes the pole before formal composition. At zero the inner series
    # 3w/(1-w) vanishes, so its first length terms need only length inputs.
    ctx.prec = precision
    ctx.cap = length
    ctx.threads = 4
    w = arb_series([0, 1])
    regular = 1 + (1 + w) * (2 + w).zeta(deflate=True)
    point_minus_two = 3 * w / (1 - w)
    polynomial = (1 - w) ** 6 * regular(point_minus_two)
    a = [polynomial[j] for j in range(length)]
    if not all(c.is_finite() for c in a):
        raise ArithmeticError("Nonfinite coefficient enclosure")
    return a


def cover_disk(a, prefix=20):
    ctx.prec = 112
    r = arb(1) / 2
    tail = sum(abs(c) * r**j for j, c in enumerate(a) if j >= prefix)
    # The entire square lies in the unit disk. This also bounds the second
    # derivative along the segment from any box center to a point in its box.
    second = sum(j * (j - 1) * abs(a[j]) for j in range(2, prefix))
    # A box center is (x+iy)/den and its half-width is 1/den.
    boxes = [(0, 0, 2)]
    certified = excluded = deepest = 0
    while boxes:
        x, y, den = boxes.pop()
        # Exact distance of the origin to this closed box, squared.
        if 4 * (max(abs(x) - 1, 0)**2 + max(abs(y) - 1, 0)**2) > den**2:
            excluded += 1
            continue
        center = acb(arb(x) / den, arb(y) / den)
        delta = arb(2) / den
        value, derivative = acb(a[prefix - 1]), acb(0)
        for c in reversed(a[:prefix - 1]):
            derivative = derivative * center + value
            value = value * center + c
        lower = abs(value) - abs(derivative) * delta - second * delta**2 / 2 - tail
        if lower > arb(65) / 1024:
            certified += 1
            deepest = max(deepest, den)
            continue
        if den >= 2**18:
            raise ArithmeticError(f"Uncertified box at ({x},{y})/{den}")
        boxes.extend((2*x + dx, 2*y + dy, 2*den) for dx in (-1, 1) for dy in (-1, 1))
    return certified, excluded, deepest, tail


def value(a, x):
    p = arb(0)
    for c in reversed(a):
        p = p * x + c
    return abs(p)


def cauchy_transfer():
    # See rational_grid.md for the Euler summation formula and the disk map.
    r = Fraction(3, 5)
    sigma = (2 - r) / (1 + r)
    size = (2 + r) / (1 - r)
    bound = (1 + r)**6 * size * (1 + (size + 1) / sigma)
    ratio = Fraction(1, 2) / r
    if bound >= 2048 or 2048 * ratio**258 / (1 - ratio) >= Fraction(1, 65536):
        raise ArithmeticError("Cauchy transfer bound failed")
    return Fraction(65, 1024) - Fraction(1, 65536)


def main():
    if flint.__version__ != "0.9.0":
        raise RuntimeError("Expected python-flint 0.9.0")
    n = 23
    length = (n + 1)**2 + 2
    mesh = length * (n + 1)
    a = coefficients(length, 1536)
    ctx.prec = 112
    slope = sum(j * abs(c) for j, c in enumerate(a))
    if not slope < 120:
        raise ArithmeticError(f"Slope bound failed: {slope.str(12)}")
    margin = Fraction(1, n + 1) + Fraction(2 * 120, mesh)
    if not margin < Fraction(1, 16):
        raise ArithmeticError("Insufficient separation")
    certified, excluded, denominator, tail = cover_disk(a)
    lower = cauchy_transfer()
    failures = []
    for k in range(15):
        section = a[:(k + 1)**2 + 2]
        x = arb(1) / (4 if k == 0 else 2)
        if not value(section, x) < arb(1) / (k + 1):
            raise ArithmeticError(f"Disk obstruction failed at n={k}")
        failures.append(k)
    fixed_failures = []
    for k in range(15, 22):
        terms = (k + 1)**2 + 2
        D = terms * (k + 1)
        nearest = (D // 2)
        v = arb(nearest) / D
        B = sum(j * abs(c) for j, c in enumerate(a[:terms]))
        if not value(a[:terms], v) < arb(1) / (k + 1) + 2 * B / D:
            raise ArithmeticError(f"Fixed-mesh obstruction failed at n={k}")
        fixed_failures.append(k)
    witnesses = []
    for k, D in [(15, 262144), (22, 12213), (23, mesh)]:
        terms = (k + 1)**2 + 2
        if not 258 <= terms <= length:
            raise ArithmeticError("Witness outside coefficient range")
        upper = Fraction(1, k + 1) + Fraction(240, D)
        if not upper < lower:
            raise ArithmeticError(f"Witness failed at n={k}")
        witnesses.append({"n": k, "terms": terms, "D": D,
                          "fixed_mesh": D == terms * (k + 1), "threshold_upper": str(upper)})
    if Fraction(1, 16) + Fraction(1, 2048) >= lower:
        raise ArithmeticError("Adaptive denominator margin failed")
    print(json.dumps({
        "field": "Q", "radius": "1/2", "n": n, "polynomial_terms": length,
        "D": mesh, "slope_enclosure": slope.str(22), "slope_upper": 120,
        "grid_threshold_upper": str(margin), "reference_section_modulus_lower": "65/1024",
        "boxes_certified": certified, "boxes_outside_disk": excluded,
        "largest_box_center_denominator": denominator, "prefix_used_in_boxes": 20,
        "remaining_polynomial_terms_uniform_bound": tail.str(16),
        "coefficient_precision_bits": 1536, "box_precision_bits": 112,
        "failed_for_every_D": failures,
        "additional_failures_at_fixed_D": fixed_failures,
        "witnesses": witnesses, "minimum_n_arbitrary_D": 15, "minimum_n_fixed_mesh": 22,
        "uniform_modulus_lower_for_all_lengths_at_least_258": str(lower),
        "all_n_at_least_15_pass_with_D": "1 + ceil(4096 * section_slope)",
        "python_flint": flint.__version__, "flint": flint.__FLINT_VERSION__,
        "verified": True,
    }, indent=2))


if __name__ == "__main__":
    main()
