"""R5/C: where do Delta_3 (and Delta_j) pairs live?  Float guidance on structured sets."""
import sys
import numpy as np
from r5_c_common import report, ring, reg

if __name__ == "__main__":
    for m in [5, 7, 9, 11, 13, 15]:
        report(f"R_{m}", reg(m), K=4)
    for m in [7, 9, 11, 13, 15, 21]:
        report(f"odd ring m={m}", ring(m), K=5)
    for m in [8, 10, 12, 16]:
        report(f"even ring m={m}", ring(m), K=5)
        report(f"even ring alt m={m}", ring(m, 'alt'), K=5)
