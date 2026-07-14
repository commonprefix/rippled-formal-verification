#!/usr/bin/env python3
# use:
# $lake env lean --run GenErrorPlotPoints.lean > points.csv
# $python3 PlotErrorPoints.py points.csv iou_mul_bound.png
"""Plot |result - truth| against |truth|*epsMulIOUToNearest for v1 = v2 IOU squaring.
Data comes from scripts_gen_points.lean (the real Lean model), as exact rationals."""
import sys
from fractions import Fraction
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

CSV = sys.argv[1] if len(sys.argv) > 1 else "points.csv"
OUT = sys.argv[2] if len(sys.argv) > 2 else "iou_mul_bound.png"

# bracket -> (title, x-scale)
META = {
    0: "Bracket 0:  |v1| ~ 10^-40 ... 10^-6   (exp field -56..-22), both signs",
    1: "Bracket 1:  exponent_field in [1, 3]   (|v1| ~ 10^16 ... 10^19)",
    2: "Bracket 2:  exponent_field in [6, 10]  (|v1| ~ 10^21 ... 10^26)",
    3: "Bracket 3:  exponent_field in [22, 32] (|v1| ~ 10^37 ... 10^48)",
}

# Parse: bracket, truthnum,truthden, errnum,errden, envnum,envden  -> floats (exact ratio then float).
data = {b: {"truth": [], "err": [], "env": []} for b in META}
with open(CSV) as f:
    for line in f:
        p = line.strip().split(",")
        if len(p) != 7:
            continue
        b = int(p[0])
        data[b]["truth"].append(float(Fraction(int(p[1]), int(p[2]))))
        data[b]["err"].append(float(Fraction(int(p[3]), int(p[4]))))
        data[b]["env"].append(float(Fraction(int(p[5]), int(p[6]))))

fig, axes = plt.subplots(2, 2, figsize=(15, 10))
for b, ax in zip(sorted(META), axes.flat):
    title = META[b]
    v1  = data[b]["truth"]
    err = data[b]["err"]
    env = data[b]["env"]
    # sort by v1 so the envelope draws as a clean line
    order = sorted(range(len(v1)), key=lambda i: v1[i])
    v1s  = [v1[i]  for i in order]
    errs = [err[i] for i in order]
    envs = [env[i] for i in order]

    ax.scatter(v1s, errs, s=4, color="#1f77b4", alpha=0.5, label="|result - truth|", zorder=3)
    ax.plot(v1s, envs, color="#ff7f0e", lw=1.3, label="|truth| * epsMulIOUToNearest", zorder=2)

    ax.set_yscale("log")
    ax.set_xscale("log")
    ax.set_title(title, fontsize=10)
    ax.set_xlabel("truth")
    ax.set_ylabel("absolute value")
    ax.grid(True, which="both", ls=":", alpha=0.4)
    ax.legend(fontsize=8, loc="upper left")

fig.suptitle("IOU multiplication (v1 = v2, to_nearest):  actual rounding error vs. the relative-error bound. result = STAmount.multiply v1 v1, truth = (v1.toRat)^2",
             fontsize=13)
fig.tight_layout(rect=[0, 0, 1, 0.97])
fig.savefig(OUT, dpi=110)
print(f"wrote {OUT}")
