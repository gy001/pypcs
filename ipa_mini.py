#!/usr/bin/env python3

# WARNING: This implementation may contain bugs and has not been audited. 
# It is only for educational purposes. DO NOT use it in production.

from pypcs.curve import Fp, Fr, ec_mul, G1Point
from merlin.merlin_transcript import MerlinTranscript

from pedersen import PedersenCommitment
import random

# Implementation of Minimal Inner Product Argument
#
#   [Groth09, Section 5.1]: Jens Groth, Linear Algebra with Sub-linear Size Zero-Knowledge Arguments
#      2009.  http://www.cs.ucl.ac.uk/staff/J.Groth/MatrixZK.pdf
#
#  Witnesses: 
#      1.  a = (a_0, ..., a_{n-1})
#      2.  b = (b_0, ..., b_{n-1})
#      3.  ab = \sum_{i=0}^{n-1} a_i b_i
#
#  Public Inputs: 
#      1.  a_cm = commit(a; r_a)
#      2.  b_cm = commit(b; r_b)
#      3.  ab_cm = commit(ab; r_ab)

PublicInputs = tuple[int, G1Point, G1Point, G1Point]
Witness = tuple[list[Fr], list[Fr], Fr]
Argument = tuple[tuple[G1Point, G1Point, G1Point, G1Point], tuple[Fr, Fr, Fr, Fr, Fr]]

class Prover:
    vec_a: list[Fr]
    vec_b: list[Fr]
    ab: Fr
    a_blinder: Fr
    b_blinder: Fr
    ab_blinder: Fr
    cm_a: G1Point
    cm_b: G1Point
    cm_ab: G1Point

    def __init__(self, wit: Witness, pcs: PedersenCommitment):
        vec_a, vec_b, ab = wit
        n = len(vec_a)

        assert n == len(vec_b)
        self.vec_a = vec_a
        self.vec_b = vec_b
        self.ab = ab
        self.rnd_gen = random.Random("schnorr-prover")

        self.a_blinder = Fr.rand(self.rnd_gen)
        self.b_blinder = Fr.rand(self.rnd_gen)
        self.ab_blinder = Fr.rand(self.rnd_gen)

        self.cm_a = pcs.commit_with_blinder(vec_a, self.a_blinder)
        self.cm_b = pcs.commit_with_blinder(vec_b, self.b_blinder)
        self.cm_ab = pcs.commit_with_blinder([ab], self.ab_blinder)
        self.pcs = pcs
        self.public_inputs = (n, self.cm_a, self.cm_b, self.cm_ab)

    def round1(self) -> G1Point:
        ra = Fr.rands(self.rnd_gen, len(self.vec_a))
        rb = Fr.rands(self.rnd_gen, len(self.vec_b))
        ra_r = Fr.rand(self.rnd_gen)
        rb_r = Fr.rand(self.rnd_gen)
        self.ra = ra
        self.rb = rb
        self.ra_r = ra_r
        self.rb_r = rb_r

        Ra = self.pcs.commit_with_blinder(ra, ra_r)
        Rb = self.pcs.commit_with_blinder(rb, rb_r)
        e0 = sum([ra[i] * rb[i] for i in range(len(ra))])
        e0_r = Fr.rand(self.rnd_gen)
        e1 = sum([self.vec_a[i] * rb[i] + self.vec_b[i] * ra[i] for i in range(len(ra))])
        e1_r = Fr.rand(self.rnd_gen)
        self.e0_r = e0_r
        self.e1_r = e1_r

        E0 = self.pcs.commit_with_blinder([e0], e0_r)
        E1 = self.pcs.commit_with_blinder([e1], e1_r)
        return (Ra, Rb, E0, E1)

    def round3(self, c: Fr) -> tuple[list[Fr], list[Fr], Fr, Fr, Fr]:
        za = [self.ra[i] + c * self.vec_a[i] for i in range(len(self.vec_a))]
        zb = [self.rb[i] + c * self.vec_b[i] for i in range(len(self.vec_b))]
        za_r = self.ra_r + c * self.a_blinder
        zb_r = self.rb_r + c * self.b_blinder
        zab_r = self.e0_r + c * self.e1_r + c**2 * self.ab_blinder
        # zz = e0_r + c * e1_r + c**2 * self.c_blinder
        return (za, zb, za_r, zb_r, zab_r)

class Verifier:
    cm_ks: G1Point
    rnd_gen: random.Random

    def __init__(self, pi: PublicInputs, pcs: PedersenCommitment):
        # public inputs
        cm_a, cm_b, cm_ab = pi
        self.cm_a = cm_a
        self.cm_b = cm_b
        self.cm_ab = cm_ab

        # pedersen commitment scheme
        self.pcs = pcs
        # random number generator
        self.rnd_gen = random.Random("schnorr-verifier")

    def round2(self, R: tuple[G1Point, G1Point, G1Point, G1Point]) -> Fr:
        c = Fr.rand(self.rnd_gen)
        self.c = c
        return c
    
    def verify(self, arg: Argument) -> bool:
        (Ra, Rb, E0, E1), (za, zb, za_r, zb_r, zab_r) = arg
        c = self.c
        cm_a = self.cm_a
        cm_b = self.cm_b
        cm_ab = self.cm_ab

        cond0 = Ra + ec_mul(self.cm_a, c) == self.pcs.commit_with_blinder(za, za_r)
        cond1 = Rb + ec_mul(cm_b, c) == self.pcs.commit_with_blinder(zb, zb_r)
        zab = sum([za[i] * zb[i] for i in range(len(za))])
        cond2 = E0 + ec_mul(E1, c) + ec_mul(cm_ab, c*c) == self.pcs.commit_with_blinder([zab], zab_r)
        print(f"cond0: {cond0}")
        print(f"cond1: {cond1}")
        print(f"cond2: {cond2}")
        return cond0 and cond1 and cond2

def run_protocol(prover: Prover, verifier: Verifier) -> bool:

    R = prover.round1()
    c = verifier.round2(R)
    z = prover.round3(c)
    return verifier.verify((R, z))

def simulate(pi: PublicInputs, verifier: Verifier, pcs: PedersenCommitment) -> Fr:

    n, cm_a, cm_b, cm_ab = pi

    rng = random.Random("schnorr-sim")

    r0, r1, r2, r3 = Fr.rands(rng, 4)
    R = (pcs.commit_with_blinder([Fr(1)], r0), pcs.commit_with_blinder([Fr(1)], r1), \
         pcs.commit_with_blinder([Fr(0)], r2), pcs.commit_with_blinder([Fr(0)], r3))

    st = verifier.rnd_gen.getstate()

    c = verifier.round2(R)

    za = Fr.rands(rng, n)
    zb = Fr.rands(rng, n)
    za_r, zb_r, zab_r = Fr.rands(rng, 3)

    Za = pcs.commit_with_blinder(za, za_r)
    Zb = pcs.commit_with_blinder(zb, zb_r)
    Ra = Za - ec_mul(cm_a, c)
    Rb = Zb - ec_mul(cm_b, c)
    
    e0, e1 = Fr.rands(rng, 2)
    ab = sum([za[i] * zb[i] for i in range(n)])
    Zab = pcs.commit_with_blinder([ab], zab_r)
    E1 = pcs.commit_with_blinder([Fr(0)], e1)
    E0 = Zab - ec_mul(cm_ab, c*c) - ec_mul(E1, c)

    # Time rewinding
    # Round 2
    verifier.rnd_gen.setstate(st)
    c_star = verifier.round2((Ra, Rb, E0, E1))
    assert c == c_star

    # Round 3

    verified = verifier.verify(((Ra, Rb, E0, E1), (za, zb, za_r, zb_r, zab_r)))
    assert verified
    return verified

# Extraction
#   to extract x = a * b
#
#      x * c^2 + x1 * c + x2 = <za, zb>
#
#      x(c0^2 - c1^2) + x_1(c0-c1) = <za0, zb0> - <za1, zb1> \\
#      x(c1^2 - c2^2) + x_1(c1-c2) = <za1, zb1> - <za2, zb2> \\
#      
#      x = [( <za0, zb0> - <za1, zb1> ) / (c0 - c1) - ( <za1, zb1> - <za2, zb2> ) / (c1 - c2)] 
#           / 
#          [(c0 + c1) - (c1 + c2)]

def extract(prover: Prover) -> Fr:
    rng = random.Random("schnorr-extract")
    n, cm_a, cm_b, cm_ab = prover.public_inputs

    R = prover.round1()
    c0, c1, c2 = Fr.rands(rng, 3)
    z0 = prover.round3(c0)
    z1 = prover.round3(c1)
    z2 = prover.round3(c2)
    za_0, zb_0, za_r0, zb_r0, zab_r0 = z0
    za_1, zb_1, za_r1, zb_r1, zab_r1 = z1
    za_2, zb_2, za_r2, zb_r2, zab_r2 = z2

    vec_a = [(za_0[i] - za_1[i])/(c0-c1) for i in range(n)]
    vec_b = [(zb_0[i] - zb_1[i])/(c0-c1) for i in range(n)]
    print(f"vec_a: {vec_a}")
    print(f"vec_b: {vec_b}")

    ab0 = sum([za_0[i] * zb_0[i] for i in range(n)])
    ab1 = sum([za_1[i] * zb_1[i] for i in range(n)])
    ab2 = sum([za_2[i] * zb_2[i] for i in range(n)])

    x = ((ab0 - ab1)/(c0 - c1) - (ab1 - ab2)/(c1 - c2)) / ((c0 + c1) - (c1 + c2))
    print(f"x: {x}")
    return x

if __name__ == "__main__":

    a = [Fr(1), Fr(2), Fr(3), Fr(4)]
    b = [Fr(6), Fr(7), Fr(8), Fr(9)]
    print(f"a={a}")
    print(f"b={b}")
    ab = sum([a[i] * b[i] for i in range(len(a))])
    print(f"ab={ab}")
    
    cms = PedersenCommitment.setup(20)
    prover = Prover((a, b, ab), cms)
    verifier = Verifier((prover.cm_a, prover.cm_b, prover.cm_ab), cms)

    print(f"protocol? : {run_protocol(prover, verifier)}")

    print(f"simulator? : {simulate(prover.public_inputs, verifier, cms)}")

    print(f"extractor? : {extract(prover)}")