#!/usr/bin/env python3

# WARNING: This implementation may contain bugs and has not been audited. 
# It is only for educational purposes. DO NOT use it in production.

from pypcs.curve import Fp, Fr, ec_mul, G1Point
from merlin.merlin_transcript import MerlinTranscript

from pedersen import PedersenCommitment
import random

# Build a simplified polynomial commitment scheme over minimal-ipa

class MinimalPCS:
    pcs: PedersenCommitment

    def __init__(self, pcs: PedersenCommitment):
        self.pcs = pcs
        self.rnd_gen = random.Random("minimal-pcs")

    def commit(self, poly: list[Fr]) -> G1Point:
        blinder = Fr.rand()
        return self.pcs.commit_with_blinder(poly, blinder), blinder
    
    def eval(self, poly: list[Fr], r: Fr, pt: Fr, v: Fr) -> Fr:
        vec_a = poly
        a_blinder = r
        n = len(vec_a)
        # round 1:
        ra = Fr.rands(self.rnd_gen, n)
        ra_rho = Fr.rand(self.rnd_gen)

        Ra = self.pcs.commit_with_blinder(ra, ra_rho)
        x_powers = [pt**i for i in range(n)]
        e0 = sum([ra[i] * x_powers[i] for i in range(n)])
        e0_rho = Fr.rand(self.rnd_gen)
        E0 = self.pcs.commit_with_blinder([e0], e0_rho)
        e1_rho = Fr.rand(self.rnd_gen)
        E1 = self.pcs.commit_with_blinder([Fr.zero()], e1_rho)

        # round 2:
        c = Fr.rand()

        # round 3:
        za = [ra[i] + c * vec_a[i] for i in range(n)]
        za_rho = ra_rho + c * a_blinder
        ze = e0_rho + c * e1_rho
        # zz = e0_r + c * e1_r + c**2 * self.c_blinder
        return (Ra, E0, E1, c, za, za_rho, ze)

    def verify(self, cm_f: G1Point, pt: Fr, v: Fr, pi: tuple[G1Point, G1Point, G1Point, Fr, list[Fr], Fr, Fr]) -> Fr:
        Ra, E0, E1, c, za, za_rho, ze = pi
        n = len(za)
        x_powers = [pt**i for i in range(n)]
        ax = sum([za[i] * x_powers[i] for i in range(n)])
        cond0 = Ra + ec_mul(cm_f, c) == self.pcs.commit_with_blinder(za, za_rho)
        C = self.pcs.commit_with_blinder([v], Fr.zero())
        cond1 = E0 + ec_mul(E1, c) + ec_mul(C, c) == self.pcs.commit_with_blinder([ax], ze)
        print(f"cond0: {cond0}")
        print(f"cond1: {cond1}")
        return cond0 and cond1

def test_mini_pcs():
    f = [Fr(1), Fr(2), Fr(3), Fr(4)]
    pt = Fr(1)
    x_powers = [pt**i for i in range(len(f))]
    v = sum([f[i] * x_powers[i] for i in range(len(f))])
    print(f"v: {v}")
    
    cms = PedersenCommitment.setup(20)
    minimal_pcs = MinimalPCS(cms)

    f_cm, f_blinder = minimal_pcs.commit(f)

    pi = minimal_pcs.eval(f, f_blinder, pt, v)
    print(f"pi: {pi}")
    assert minimal_pcs.verify(f_cm, pt, v, pi)

if __name__ == "__main__":
    test_mini_pcs()
