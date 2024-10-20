#!/usr/bin/env python3

# WARNING: This implementation may contain bugs and has not been audited. 
# It is only for educational purposes. DO NOT use it in production.

from pypcs.curve import Fp, Fr, ec_mul, G1Point
import random

from merlin.merlin_transcript import MerlinTranscript
from pedersen import PedersenCommitment


# (HV) Perfect Zero-Knowledge Schnorr Protocol

cms = PedersenCommitment.setup(40)

class Prover:
    ks: list[Fr]
    blinders: list[Fr]
    Ks: list[G1Point]

    def __init__(self, ks: list[Fr]):
        self.ks = ks
        self.rnd_gen = random.Random("schnorr-prover")
        self.blinders = Fr.rands(self.rnd_gen, len(self.ks))
        self.Ks = [cms.commit_with_blinder([ks[i]], self.blinders[i]) for i in range(len(ks))]

    def round1(self) -> G1Point:
        r = Fr.rand(rndg=self.rnd_gen)
        r_blinder = Fr.rand(rndg=self.rnd_gen)
        self.r, self.r_blinder = r, r_blinder
        R = cms.commit_with_blinder([r], r_blinder)
        return R

    def round3(self, c: Fr) -> tuple[Fr, Fr]:
        z = self.r
        zr = self.r_blinder
        x = c
        for i in range(len(self.ks)):
            z  += x * self.ks[i]
            zr += x * self.blinders[i]
            x *= c
        return z, zr

class Verifier:
    Ks: list[G1Point]
    rnd_gen: random.Random

    def __init__(self, Ks: G1Point):
        self.Ks = Ks
        self.rnd_gen = random.Random("schnorr-verifier")

    def round2(self, R: G1Point) -> Fr:
        c = Fr.rand(rndg=self.rnd_gen)
        return c
    
    def verify(self, R: G1Point, c: Fr, z: tuple[Fr, Fr]) -> bool:
        C = R
        e = c
        for i in range(len(self.Ks)):
            C += ec_mul(self.Ks[i], e)
            e *= c
        return cms.commit_with_blinder([z[0]], z[1]) == C

def run_schnorr(prover: Prover, verifier: Verifier) -> bool:

    R = prover.round1()
    c = verifier.round2(R)
    z = prover.round3(c)
    return verifier.verify(R, c, z)


def run_schnorr_non_interactive(prover: Prover) -> bool:

    transcript = MerlinTranscript(b"schnorr")
    transcript.append_message(b"Ks", str(prover.Ks).encode())

    R = prover.round1()

    transcript.append_message(b"R", str(R).encode())

    c_bytes = transcript.challenge_bytes(b"challenge", 32)
    c = Fr(int.from_bytes(c_bytes, "big"))

    z = prover.round3(c)

    print(f"len(c_bytes)={len(c_bytes)}")
    print(f"c={c}")

    return verifier.verify(R, c, z)

def simulate(prover_pk: G1Point, verifier: Verifier) -> Fr:
    raise NotImplementedError

def extract(prover: Prover) -> Fr:
    raise NotImplementedError


if __name__ == "__main__":
    ks = [Fr(31), Fr(32), Fr(33)]
    print(f"ks: {ks}")

    prover = Prover(ks)
    verifier = Verifier(prover.Ks)

    print(f"protocol? : {run_schnorr(prover, verifier)}")

    print(f"run_schnorr_non_interactive(prover) : {run_schnorr_non_interactive(prover)}")

    # print(f"simulator? : {simulate(prover.pk, verifier)}")

    # print(f"extractor? : {extract(Prover(sk))}")