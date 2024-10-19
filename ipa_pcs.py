#!/usr/bin/env python3

# WARNING: This implementation may contain bugs and has not been audited. 
# It is only for educational purposes. DO NOT use it in production.

from pypcs.curve import Fp, Fr, ec_mul, G1Point
from merlin.merlin_transcript import MerlinTranscript

from pedersen import PedersenCommitment

# WARNING: 
#   1. For demonstration, we deliberately use an insecure random number 
#      generator, random.Random. To generate secure randomness, use 
#      the standard library `secrets` instead.
#        
#      See more here: https://docs.python.org/3/library/secrets.html
#
#   2. Challenges are only 1 byte long for simplicity, which is not secure.

import random

# Implementation of the BulletproofIPA PCS from the following paper:
#   Bulletproofs: https://eprint.iacr.org/2017/1066.pdf
#
# The implementation of ZK is slightly different from the original 
# paper. The original paper adds a Vector Schnorr protocol on the 
# outer layer, while this implementation uses the method from the 
# Hyrax paper, adding two blinders in each recursive round, 
# and then using a Schnorr protocol (in the inner layer) to open 
# in the final open phase.
#
#   Hyrax: https://eprint.iacr.org/2017/1132.pdf


# TODO:
# - add options for the blinders
# - add batch proving and verifying


IPA_PCS_Argument = tuple[int,G1Point, G1Point, G1Point, list[Fr]]

class IPA_PCS:

    pcs: PedersenCommitment

    def __init__(self, pcs: PedersenCommitment):
        """
        Args:
            pcs: the PedersenCommitment instance to use for the proof
        """
        self.pcs = pcs
        self.rnd_gen = random.Random("ipa-pcs")

    def commit(self, vec_c: list[Fr]) -> tuple[G1Point, Fr]:
        """
        Commit to a vector of coefficients.
        """

        blinder = Fr.rand()
        return self.pcs.commit(vec_c, blinder), blinder
    
    def eval_prove(self, f_cm: G1Point, x: Fr, y: Fr, vec_c: list[Fr], rho_c: Fr, tr: MerlinTranscript, debug=False) -> IPA_PCS_Argument:
        """
        Prove that a polynomial f(x) = y.

            f(X) = c0 + c1 * X + c2 * X^2 + ... + cn * X^n

        Args:
            f_cm: the commitment to the polynomial f(X)
            x: the challenge point
            y: the evaluation of f(x)
            vec_c: the coeffcient vector of the polynomial f(X)
            rho_c: the blinding factor for the commitment to vec_c
            tr: the Merlin transcript to use for the proof
            debug: whether to print debug information
        Returns:
            an IPA_PCS_Argument tuple
        """
        n = len(vec_c)
        assert len(self.pcs.pp) >= 2 * n + 1, f"EROR: len(pcs.pp) = {len(self.pcs.pp)}, while len(vec_c) = {len(vec_c)}"
        if debug:
            print(f"prove> n: {n}")
        rng = random.Random(b"schnorr-1folding-commit")

        G = self.pcs.pp[:n]
        H = self.pcs.pp[-2]
        U = self.pcs.pp[-1]

        tr.append_message(b"f_cm", str(f_cm).encode())
        tr.append_message(b"x", str(x).encode())
        tr.append_message(b"y", str(y).encode())

        vec_x = [x**i for i in range(n)]

        # Round 1:   gamma <~ Fr 

        # WARN: challenge should be 32 bytes long, here we use 1 byte for debugging
        gamma = Fr.from_bytes(tr.challenge_bytes(b"gamma", 1))

        Ugamma = ec_mul(U, gamma)
        P = f_cm + ec_mul(Ugamma, y)
        PLR = []
        rho = rho_c

        # Round 2:   PL, PR, ->
        round = 0
        half = n // 2

        while half > 0:
            if debug:
                print(f"prove> round: {round}")
            round += 1
            G1 = G[:half]
            G2 = G[half:]
            cs1 = vec_c[:half]
            cs2 = vec_c[half:]
            xs1 = vec_x[:half]
            xs2 = vec_x[half:]
            rho_L, rho_R = Fr.rands(rng, 2)

            PL = self.pcs.commit_with_pp(G1, cs2) + ec_mul(Ugamma, ipa(cs2, xs1)) + ec_mul(H, rho_L)
            PR = self.pcs.commit_with_pp(G2, cs1) + ec_mul(Ugamma, ipa(cs1, xs2)) + ec_mul(H, rho_R)
            PLR.insert(0, (PL, PR))

            tr.append_message(b"PL", str(PL).encode())
            tr.append_message(b"PR", str(PR).encode())

            # Round 3:   mu <~ Fr
            mu = Fr.from_bytes(tr.challenge_bytes(b"mu", 1))
            if debug:
                print(f"prove> mu: {mu}")
            vec_c = [cs1[i] + mu * cs2[i] for i in range(half)]
            vec_x = [xs1[i] + mu.inv() * xs2[i] for i in range(half)]
            rho += rho_L * mu + rho_R * mu.inv()

            G = [G1[i] + ec_mul(G2[i], mu.inv()) for i in range(half)]

            # Debug
            if debug:
                lhs = self.pcs.commit_with_pp(G, vec_c) + ec_mul(Ugamma, ipa(vec_c, vec_x)) + ec_mul(H, rho)
                P += ec_mul(PL, mu) + ec_mul(PR, mu.inv())
                if lhs == P:
                    print(f"prove> [vec_c]_(G) + [<vec_c, vec_x>]_(H) == P + mu*PL + mu^(-1)*PR ok ")
                else:
                    print(f"prove> [vec_c]_(G) + [<vec_c, vec_x>]_(H) == P + mu*PL + mu^(-1)*PR failed ")
            half = half // 2

        assert len(vec_c) == len(vec_x) == len(G) == 1, "EROR: len(vec_c) and len(vec_x) should be 1"
        c0 = vec_c[0]
        x0 = vec_x[0]
        G0 = G[0]

        # Round 4:  R -> 
        G_new = G0 + ec_mul(Ugamma, x0)
        r, rho_r = Fr.rands(rng, 2)
        R = ec_mul(G_new, r) + ec_mul(H, rho_r)
        tr.append_message(b"R", str(R).encode())

        # Round 5:  zeta <~ Fr
        zeta = Fr.from_bytes(tr.challenge_bytes(b"zeta", 1))
        if debug:
            print(f"prove> zeta: {zeta}")

        # Round 6:  z ->  
        z = r + zeta * c0
        z_r = rho_r + zeta * rho
    
        # Debug
        if debug:
            lhs = self.pcs.commit_with_pp([G_new], [z])
            rhs = P + ec_mul(G_new, r) + ec_mul(P, zeta)
            if lhs == rhs:
                print(f"prove> [z]_(G_new) == pcs.commit_with_pp(G, vec_z) ok ")
            else:
                print(f"prove> Z == pcs.commit_with_pp(G, vec_z) failed ")

            return (n, PLR, R, z, z_r)
        
    def eval_verify(self, f_cm: G1Point, x: Fr, y: Fr, arg: IPA_PCS_Argument, tr: MerlinTranscript, debug=False) -> bool:
        """
        Verify an evaluation argument for a polynomial f, st. f(x) = y.

            f(X) = c0 + c1 * X + c2 * X^2 + ... + cn * X^n

        Args:
            f_cm: the commitment to the polynomial f(X)
            x: the challenge point
            y: the evaluation of f(x)
            arg: the IPA_PCS_Argument (proof transcript)
            tr: the Merlin transcript to use for the proof
            debug: whether to print debug information
        """

        n, PLR, R, z, z_r = arg
        vec_x = [x**i for i in range(n)]

        tr.append_message(b"f_cm", str(f_cm).encode())
        tr.append_message(b"x", str(x).encode())
        tr.append_message(b"y", str(y).encode())

        G = self.pcs.pp[:n]
        H = self.pcs.pp[-2]
        U = self.pcs.pp[-1]

        # Round 1:   gamma <~ Fr 

        # WARN: challenge should be 32 bytes long, here we use 1 byte for debugging
        gamma = Fr.from_bytes(tr.challenge_bytes(b"gamma", 1))
        if debug:
            print(f"verify> gamma: {gamma}")

        Ugamma = ec_mul(U, gamma)
        P = f_cm + ec_mul(Ugamma, y)

        # Round 2:   PL, PR, ->
        round = 0
        half = n // 2
        while half > 0:
            PL, PR = PLR.pop()

            tr.append_message(b"PL", str(PL).encode())
            tr.append_message(b"PR", str(PR).encode())

            # Round 3:   mu <~ Fr
            mu = Fr.from_bytes(tr.challenge_bytes(b"mu", 1))
            if debug:
                print(f"verify> mu: {mu}")

            G1 = G[:half]
            G2 = G[half:]
            xs1 = vec_x[:half]
            xs2 = vec_x[half:]
            G = [G1[i] + ec_mul(G2[i], mu.inv()) for i in range(half)]
            vec_x = [xs1[i] + mu.inv() * xs2[i] for i in range(half)]
            
            # print(f"verify> G[{round}]: {G}")

            # Z_1 ?= Z + x * AL + x^{-1} * AR
        
            P += ec_mul(PL, mu) + ec_mul(PR, mu.inv())
            half = half // 2
            round += 1
        
        assert len(G) == len(vec_x) == 1, "EROR: len(vec_c) and len(vec_x) should be 1"
        G0 = G[0]
        x0 = vec_x[0]

        # Round 4:  R -> 
        tr.append_message(b"R", str(R).encode())

        # Round 5:  zeta <~ Fr
        zeta = Fr.from_bytes(tr.challenge_bytes(b"zeta", 1))
        if debug:
            print(f"verify> zeta: {zeta}")

        # Round 6:  z ->  
        
        G_new = G0 + ec_mul(Ugamma, x0)
        rhs = R + ec_mul(P, zeta)
        lhs = self.pcs.commit_with_pp([G_new, H], [z, z_r])

        return lhs == rhs

def ipa(vec_a: list[Fr], vec_b: list[Fr]) -> Fr:
    n = len(vec_a)
    assert len(vec_b) == n
    return sum(a * b for a, b in zip(vec_a, vec_b))

def test_ipa_pcs():

    # initialize the PedersenCommitment and the IPA_PCS
    pcs = PedersenCommitment.setup(20)
    ipa_pcs = IPA_PCS(pcs)
    tr = MerlinTranscript(b"ipa-pcs")

    # A simple instance f(x) = y
    vec_c = [Fr(2), Fr(3), Fr(4), Fr(5), Fr(6), Fr(7), Fr(8), Fr(9)]
    x = Fr(4)
    vec_x = [x**i for i in range(len(vec_c))]
    y = ipa(vec_c, vec_x)

    # commit to the polynomial
    rho_c = Fr.rand()
    G = pcs.pp[:len(vec_c)]
    H = pcs.pp[-2]
    f_cm = pcs.commit_with_pp(G, vec_c) + ec_mul(H, rho_c)

    # fork the transcript for both prover and verifier
    tr_prover = tr.fork(b"prover")
    tr_verifier = tr.fork(b"verifier")

    # prover proves f(x) = y and sends an argument to the verifier
    arg = ipa_pcs.eval_prove(f_cm, x, y, vec_c, rho_c, tr_prover, debug=True)
    print(f"arg: {arg}")

    # verifier verifies the argument
    verified = ipa_pcs.eval_verify(f_cm, x, y, arg, tr_verifier, debug=True)
    print(f"verified: {verified}")

if __name__ == "__main__":
    test_ipa_pcs()