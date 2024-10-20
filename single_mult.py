#!/usr/bin/env python3

# WARNING: This implementation may contain bugs and has not been audited. 
# It is only for educational purposes. DO NOT use it in production.

from pypcs.curve import Fp, Fr, ec_mul, G1Point
import random
from pedersen import PedersenCommitment

cms = PedersenCommitment.setup(20)

# Implement a single multiplication argument (∑-protocol)
#
# The scheme is from Section 5.3 of [BG12]: 
#   - Efficient Zero-Knowledge Argument for Correctness of a Shuffle.
#   - Stephanie Bayer and Jens Groth: 
#   - http://www.cs.ucl.ac.uk/staff/J.Groth/MinimalShuffle.pdf
#

class Prover:
    a: Fr
    b: Fr
    c: Fr
    A: G1Point
    B: G1Point
    C: G1Point

    def __init__(self, a: Fr, b: Fr, c: Fr):
        self.a = a
        self.b = b
        self.c = c
        self.rnd_gen = random.Random("schnorr-prover")
        self.a_blinder = Fr.rand(self.rnd_gen)
        self.b_blinder = Fr.rand(self.rnd_gen)
        self.c_blinder = Fr.rand(self.rnd_gen)
        self.A = cms.commit_with_blinder([a], self.a_blinder)
        self.B = cms.commit_with_blinder([b], self.b_blinder)
        self.C = cms.commit_with_blinder([c], self.c_blinder)

    def round1(self) -> tuple[G1Point, G1Point, G1Point]:
        ra = Fr.rand(self.rnd_gen)
        ra_r = Fr.rand(self.rnd_gen)
        rb = Fr.rand(self.rnd_gen)
        rb_r = Fr.rand(self.rnd_gen)
        rt = Fr.rand(self.rnd_gen)
        
        Ra = cms.commit_with_blinder([ra], ra_r)
        Rb = cms.commit_with_blinder([rb], rb_r)
        Rt = ec_mul(self.B, ra) + cms.commit_with_blinder([Fr.zero()], -rt)
        self.r = (ra, rb, rt, ra_r, rb_r)
        return (Ra, Rb, Rt)

    def round3(self, e: Fr) -> tuple[Fr, Fr, Fr, Fr, Fr]:
        za = self.r[0] + e * self.a
        zb = self.r[1] + e * self.b
        za_r = self.r[3] + e * self.a_blinder
        zb_r = self.r[4] + e * self.b_blinder
        zt_r = self.r[2] + e * (self.a * self.b_blinder - self.c_blinder)

        return (za, zb, za_r, zb_r, zt_r)

class Verifier:
    pk: G1Point
    rnd_gen: random.Random

    def __init__(self, A: G1Point, B: G1Point, C: G1Point):
        self.A = A
        self.B = B
        self.C = C
        self.rnd_gen = random.Random("schnorr-verifier")

    def round2(self, R: tuple[G1Point, G1Point, G1Point]) -> Fr:
        e = Fr.rand(self.rnd_gen)
        return e
    
    def verify(self, R: tuple[G1Point, G1Point, G1Point], e: Fr, zs: tuple[Fr, Fr, Fr, Fr, Fr]) -> bool:
        Ra = R[0]
        Rb = R[1]
        Rt = R[2]
        cond0 = cms.commit_with_blinder([zs[0]], zs[2]) ==  ec_mul(self.A, e) + Ra 
        cond1 = cms.commit_with_blinder([zs[1]], zs[3]) ==  ec_mul(self.B, e) + Rb 
        cond2 = ec_mul(self.B, zs[0]) ==  ec_mul(self.C, e) + Rt + cms.commit_with_blinder([Fr.zero()], zs[4])
        print(f"cond0: {cond0}")
        print(f"cond1: {cond1}")
        print(f"cond2: {cond2}")
        return cond0 and cond1 and cond2
    

def run_schnorr(prover: Prover, verifier: Verifier) -> bool:

    R = prover.round1()
    c = verifier.round2(R)
    z = prover.round3(c)
    return verifier.verify(R, c, z)

def simulate(prover_pk: G1Point, verifier: Verifier) -> Fr:
    raise NotImplementedError("Not implemented")

def extract(prover: Prover) -> Fr:
    raise NotImplementedError("Not implemented")

if __name__ == "__main__":
    a = Fr(4)
    b = Fr(5)
    c = Fr(20)

    prover = Prover(a, b, c)
    verifier = Verifier(prover.A, prover.B, prover.C)

    print(f"Fr(2)={Fr(2)}")
    print(f"Fr(-2)={Fr(-2)}")

    print(f"protocol? : {run_schnorr(prover, verifier)}")

    # TODO: implement simulator and extractor
    # print(f"simulator? : {simulate(prover.pk, verifier)}")
    # print(f"extractor? : {extract(Prover(sk))}")